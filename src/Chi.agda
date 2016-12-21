------------------------------------------------------------------------
-- A specification of the language χ
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Atom

-- The specification is parametrised by an instance of χ-atoms.

module Chi (atoms : χ-atoms) where

open import Equality.Propositional
open import Prelude hiding (const)

open χ-atoms atoms

-- Abstract syntax.

mutual

  data Exp : Set where
    apply  : Exp → Exp → Exp
    lambda : Var → Exp → Exp
    case   : Exp → List Br → Exp
    rec    : Var → Exp → Exp
    var    : Var → Exp
    const  : Const → List Exp → Exp
    halts  : Exp → Exp

  data Br : Set where
    branch : Const → List Var → Exp → Br


postulate
  code : Exp → Exp

-- Substitution.

mutual

  infix 6 _[_←_] _[_←_]B _[_←_]⋆ _[_←_]B⋆

  _[_←_] : Exp → Var → Exp → Exp
  apply e₁ e₂ [ x ← e′ ] = apply (e₁ [ x ← e′ ]) (e₂ [ x ← e′ ])
  lambda y e  [ x ← e′ ] = lambda y (if x V.≟ y
                                     then e
                                     else e [ x ← e′ ])
  case e bs [ x ← e′ ]   = case (e [ x ← e′ ]) (bs [ x ← e′ ]B⋆)
  rec y e   [ x ← e′ ]   = rec y (if x V.≟ y
                                  then e
                                  else e [ x ← e′ ])

  var y [ x ← e′ ]       = if x V.≟ y then e′ else var y
  const c es  [ x ← e′ ] = const c (es [ x ← e′ ]⋆)
  halts e     [ x ← e′ ] = halts (e [ x ← e′ ])

  _[_←_]B : Br → Var → Exp → Br
  branch c xs e [ x ← e′ ]B with V.member x xs
  ... | yes _ = branch c xs e
  ... | no  _ = branch c xs (e [ x ← e′ ])

  _[_←_]⋆ : List Exp → Var → Exp → List Exp
  []       [ x ← e′ ]⋆ = []
  (e ∷ es) [ x ← e′ ]⋆ = e [ x ← e′ ] ∷ es [ x ← e′ ]⋆

  _[_←_]B⋆ : List Br → Var → Exp → List Br
  []       [ x ← e′ ]B⋆ = []
  (b ∷ bs) [ x ← e′ ]B⋆ = b [ x ← e′ ]B ∷ bs [ x ← e′ ]B⋆

infix 5 ∷_
infix 4 _[_←_]↦_

data _[_←_]↦_ (e : Exp) : List Var → List Exp → Exp → Set where
  [] : e [ [] ← [] ]↦ e
  ∷_ : ∀ {x xs e′ es′ e″} →
       e [ xs ← es′ ]↦ e″ → e [ x ∷ xs ← e′ ∷ es′ ]↦ e″ [ x ← e′ ]

-- Operational semantics.

data Lookup (c : Const) : List Br → List Var → Exp → Set where
  here  : ∀ {xs e bs} → Lookup c (branch c xs e ∷ bs) xs e
  there : ∀ {c′ xs′ e′ bs xs e} →
          c ≢ c′ → Lookup c bs xs e →
          Lookup c (branch c′ xs′ e′ ∷ bs) xs e

infixr 5 _∷_
infix 4 _⟶_ _⟶⋆_

mutual

  data _⟶_ : Exp → Exp → Set where
    apply  : ∀ {e₁ e₂ x e v₂ v} →
             e₁ ⟶ lambda x e → e₂ ⟶ v₂ → e [ x ← v₂ ] ⟶ v →
             apply e₁ e₂ ⟶ v
    case   : ∀ {e bs c es xs e′ e″ v} →
             e ⟶ const c es → Lookup c bs xs e′ →
             e′ [ xs ← es ]↦ e″ → e″ ⟶ v →
             case e bs ⟶ v
    rec    : ∀ {x e v} → e [ x ← rec x e ] ⟶ v → rec x e ⟶ v
    lambda : ∀ {x e} → lambda x e ⟶ lambda x e
    const  : ∀ {c es vs} → es ⟶⋆ vs → const c es ⟶ const c vs

  data _⟶⋆_ : List Exp → List Exp → Set where
    []  : [] ⟶⋆ []
    _∷_ : ∀ {e es v vs} → e ⟶ v → es ⟶⋆ vs → e ∷ es ⟶⋆ v ∷ vs




infix 4 _/_⟶_ _/_⟶⋆_

open import SizeLt

postulate
  `true `false : Exp

mutual

  data _/_⟶_ (D : Exp → Set) : Exp → Exp → Set where
    apply  : ∀ {e₁ e₂ x e v₂ v} →
             D / e₁ ⟶ lambda x e → D / e₂ ⟶ v₂ → D / e [ x ← v₂ ] ⟶ v →
             D / apply e₁ e₂ ⟶ v
    case   : ∀ {e bs c es xs e′ e″ v} →
             D / e ⟶ const c es → Lookup c bs xs e′ →
             e′ [ xs ← es ]↦ e″ → D / e″ ⟶ v →
             D / case e bs ⟶ v
    rec    : ∀ {x e v} → D / e [ x ← rec x e ] ⟶ v → D / rec x e ⟶ v
    lambda : ∀ {x e} → D / lambda x e ⟶ lambda x e
    const  : ∀ {c es vs} → D / es ⟶⋆ vs → D / const c es ⟶ const c vs
    halts1 : ∀ {e e′ v} → D / e ⟶ code e′ → D / e′ ⟶ v → D / halts e ⟶ `true
    halts2 : ∀ {e e′} → D / e ⟶ code e′ → D e → D / halts e ⟶ `false

  data _/_⟶⋆_ (i : Exp → Set) : List Exp → List Exp → Set where
    []  : i / [] ⟶⋆ []
    _∷_ : ∀ {e es v vs} → i / e ⟶ v → i / es ⟶⋆ vs → i / e ∷ es ⟶⋆ v ∷ vs

mutual

  _/′_⟶_ : Size → Exp → Exp → Set
  i /′ e ⟶ v = Diverge i / e ⟶ v

  Diverge : Size → Exp → Set
  Diverge i e = ∀ (j : SizeLt i){v} → DivergeLt j / e ⟶ v → ⊥ {lzero}

  DivergeLt : {i : Size} (j : SizeLt i) → Exp → Set
  DivergeLt (lt j) e = Diverge j e
