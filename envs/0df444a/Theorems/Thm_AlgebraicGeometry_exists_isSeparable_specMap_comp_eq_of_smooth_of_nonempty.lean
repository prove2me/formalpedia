-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isSeparable_specMap_comp_eq_of_smooth_of_nonempty
-- name    : AlgebraicGeometry.exists_isSeparable_specMap_comp_eq_of_smooth_of_nonempty
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/8418be4b-6187-5b03-921d-8d4cd1ea6879
-- title:
--   Smooth non-empty K-schemes have finite separable points
-- statement:
--   Let $K$ be a field and let $g \colon V \to \operatorname{Spec} K$ be a morphism of schemes (all in a fixed universe) which is smooth, with $V$ non-empty. Then there exist a type $K'$ carrying a field structure, an algebra structure of $K$ on $K'$ making $K'$ a finite-dimensional $K$-vector space and a separable $K$-algebra, together with a morphism of schemes $P \colon \operatorname{Spec} K' \to V$, such that $P$ followed by $g$ equals the morphism $\operatorname{Spec} K' \to \operatorname{Spec} K$ induced by the structure map $K \to K'$ of the algebra. In other words, $V$ has a point with values in some finite separable extension field $K'$ of $K$, this point being a morphism over $\operatorname{Spec} K$. The data $K'$, its field, algebra, finiteness and separability structures, and the point $P$ are all produced existentially; no control is asserted over the degree of $K'/K$ or over the image of $P$.
--
--   This is the standard fact that a non-empty smooth scheme over a field acquires a point after a finite separable extension of the base, equivalently that its points over a separable closure are non-empty. It is used in the present development to produce points of smooth schemes over Henselian local rings and, through that, in the construction of the relative group law on Jacobians with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isSeparable_specMap_comp_eq_of_smooth_of_nonempty.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_isSeparable_specMap_comp_eq_of_smooth_of_nonempty
    (K : Type u) [Field K] {V : Scheme.{u}} (g : V ⟶ Spec (CommRingCat.of K)) [Smooth g] [Nonempty V] :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K')
      (_ : Algebra.IsSeparable K K') (P : Spec (CommRingCat.of K') ⟶ V),
      P ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K K')) := by sorry
