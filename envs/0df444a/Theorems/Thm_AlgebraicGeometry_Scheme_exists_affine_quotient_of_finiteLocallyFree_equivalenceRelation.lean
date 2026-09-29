-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_affine_quotient_of_finiteLocallyFree_equivalenceRelation
-- name    : AlgebraicGeometry.Scheme.exists_affine_quotient_of_finiteLocallyFree_equivalenceRelation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/b73039f9-8385-5400-929c-da1d0505bae1
-- title:
--   Affine quotient by a finite locally free equivalence relation
-- statement:
--   Let $X$ and $R$ be schemes with $X$ affine, and let $s,t \colon R \to X$ be two morphisms, each finite, flat and locally of finite presentation. Assume that the pair $(s,t)$ is jointly monomorphic, in the sense that for every scheme $T$ and morphisms $a,b \colon T \to R$ with $a \mathbin{;} s = b \mathbin{;} s$ and $a \mathbin{;} t = b \mathbin{;} t$ one has $a = b$; and assume that for every scheme $T$ the relation on $T$-valued points of $X$ given by $x \sim y$ iff there is $\varphi \colon T \to R$ with $\varphi \mathbin{;} s = x$ and $\varphi \mathbin{;} t = y$ is an equivalence relation. Then there exist an affine scheme $Y$, a morphism $p \colon X \to Y$ and a proof $w$ that $s \mathbin{;} p = t \mathbin{;} p$, such that $p$ is finite, flat, locally of finite presentation and surjective, the square with sides $s, t$ and $p, p$ is cartesian (so $(R;s,t)$ is the kernel pair of $p$), and the cofork on $s,t$ determined by $p$ and $w$ is a colimit, i.e. $p$ is a coequaliser of $s$ and $t$ in the category of schemes. No affineness is assumed of $R$.
--
--   This is the effectivity of a finite locally free equivalence relation on an affine scheme: the quotient exists, is affine, and the quotient map is finite locally free and surjective with the given relation as its kernel pair; concretely $Y$ is the spectrum of the ring of functions $a$ on $X$ with $s^{*}a = t^{*}a$. It is the scheme-theoretic form of the ring-level statement [`RingHom.isPushout_eqLocus_of_finiteLocallyFree_equivalenceRelation`](thm.html#RingHom.isPushout_eqLocus_of_finiteLocallyFree_equivalenceRelation) (pushout of rings against pullback of affine schemes), and it feeds the general, non-affine quotient construction [`AlgebraicGeometry.Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation`](thm.html#AlgebraicGeometry.Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation), the production of invariant affine opens, and the universality statement for relative effective Cartier divisors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_affine_quotient_of_finiteLocallyFree_equivalenceRelation.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.exists_affine_quotient_of_finiteLocallyFree_equivalenceRelation
    {X R : Scheme.{u}} [IsAffine X] (s t : R ⟶ X)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    [IsFinite t] [Flat t] [LocallyOfFinitePresentation t]
    (hmono : ∀ {T : Scheme.{u}} (a b : T ⟶ R), a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b)
    (hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y) :
    ∃ (Y : Scheme.{u}) (_ : IsAffine Y) (p : X ⟶ Y) (w : s ≫ p = t ≫ p),
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback s t p p ∧ Nonempty (IsColimit (Cofork.ofπ p w)) := by sorry
