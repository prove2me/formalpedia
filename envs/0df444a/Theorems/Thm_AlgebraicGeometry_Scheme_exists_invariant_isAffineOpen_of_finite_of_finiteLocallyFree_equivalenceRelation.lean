-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_invariant_isAffineOpen_of_finite_of_finiteLocallyFree_equivalenceRelation
-- name    : AlgebraicGeometry.Scheme.exists_invariant_isAffineOpen_of_finite_of_finiteLocallyFree_equivalenceRelation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/f05b0e59-3efe-5b4c-ad5d-8c3416586a51
-- title:
--   Invariant affine open through a finite set of points
-- statement:
--   Let $X$ and $R$ be schemes and let $s, t \colon R \to X$ be two morphisms, each assumed finite, flat and locally of finite presentation. Assume that for every scheme $T$ the relation on $T$-valued points of $X$ given by $x \sim y$ if and only if there exists $\varphi \colon T \to R$ with $x = s \circ \varphi$ and $y = t \circ \varphi$ (in diagrammatic notation $\varphi \gg\!\!> s = x$ and $\varphi \gg\!\!> t = y$) is an equivalence relation on the set of morphisms $T \to X$. Let $S$ be a finite set of points of $X$ and let $U$ be an open subset of $X$ which is affine, and suppose that for every $x \in S$ and every point $r$ of $R$ with $s(r) = x$ one has $t(r) \in U$, i.e. $t(s^{-1}(x)) \subseteq U$ for all $x \in S$. The conclusion is that there exists an open subset $W$ of $X$ which is affine, contains $S$, is contained in $U$, and satisfies $s^{-1}(W) = t^{-1}(W)$ as open subsets of $R$.
--
--   This is the several-points version of the standard construction of an $R$-invariant affine open neighbourhood for a finite locally free equivalence relation on a scheme, the usual statement being the case $S = \{x\}$; the strengthening to a finite set $S$ is what allows the property that every finite set of points lies in an affine open to be transported to a quotient. It is used in the proof of [`AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_forall_preimage_mem_of_isFinite_of_flat_of_surjective`](thm.html#AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_forall_preimage_mem_of_isFinite_of_flat_of_surjective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_invariant_isAffineOpen_of_finite_of_finiteLocallyFree_equivalenceRelation.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.exists_invariant_isAffineOpen_of_finite_of_finiteLocallyFree_equivalenceRelation
    {X R : Scheme.{u}} (s t : R ⟶ X)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    [IsFinite t] [Flat t] [LocallyOfFinitePresentation t]
    (hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y)
    {S : Set X} (hS : S.Finite) {U : X.Opens} (hU : IsAffineOpen U)
    (hSU : ∀ x ∈ S, ∀ r : R, s r = x → t r ∈ U) :
    ∃ W : X.Opens, IsAffineOpen W ∧ S ⊆ (W : Set X) ∧ W ≤ U ∧ s ⁻¹ᵁ W = t ⁻¹ᵁ W := by sorry
