-- Prove2me | Theorems.Thm_AlgebraicGeometry_Smooth_exists_orderedAffineCover_forall_exists_smooth_isPullback_of_surjective_of_forall_isNilpotent
-- name    : AlgebraicGeometry.Smooth.exists_orderedAffineCover_forall_exists_smooth_isPullback_of_surjective_of_forall_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/534b920e-c252-526c-ba60-f28df18800e2
-- title:
--   Finite ordered affine cover with smooth affine liftings
-- statement:
--   Let $p \colon S \to S_0$ be a homomorphism of commutative rings (both types in the same universe $u$) which is surjective and whose kernel consists of nilpotent elements, and let $f_0 \colon X_0 \to \operatorname{Spec} S_0$ be a morphism of schemes that is smooth and quasi-compact. Then there exists an ordered affine cover $\mathcal{U}$ of $X_0$, that is: a finite linearly ordered index type $\iota$ together with opens $\mathcal{U}.U i \subseteq X_0$, each of which is an affine open, whose supremum is all of $X_0$; and this cover has the property that for every index $i$ and every open $V \subseteq X_0$ which is affine and satisfies $V \le \mathcal{U}.U i$, there are a scheme $Y$, a morphism $q \colon Y \to \operatorname{Spec} S$ and a morphism $g \colon V \to Y$ such that $Y$ is affine, $q$ is smooth, and the square with top edge $g$, left edge the composite of the inclusion $V \hookrightarrow X_0$ followed by $f_0$, right edge $q$ and bottom edge $\operatorname{Spec}$ of $p$ is cartesian. Thus $V \cong Y \times_{\operatorname{Spec} S} \operatorname{Spec} S_0$: each such $V$ admits a smooth affine lift over $S$.
--
--   This is the finite-cover packaging of the local lifting (deformation) theorem for smooth morphisms along a surjection with nilpotent kernel: smoothness makes affine pieces of $X_0$ deformable from $S_0$ to $S$, and the ordered affine cover supplies the indexing needed for Čech-theoretic arguments. It is used in the construction of smooth lifts in the good-reduction analysis of Jacobians, via [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_smooth_isPullback_of_ker_mul_maximalIdeal_eq_bot_of_le_cechFinrank`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_smooth_isPullback_of_ker_mul_maximalIdeal_eq_bot_of_le_cechFinrank).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Smooth_exists_orderedAffineCover_forall_exists_smooth_isPullback_of_surjective_of_forall_isNilpotent.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Smooth.exists_orderedAffineCover_forall_exists_smooth_isPullback_of_surjective_of_forall_isNilpotent
    {S S₀ : Type u} [CommRing S] [CommRing S₀] (p : S →+* S₀) (hp : Function.Surjective p)
    (hnil : ∀ x ∈ RingHom.ker p, IsNilpotent x)
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of S₀)) [Smooth f₀] [QuasiCompact f₀] :
    ∃ 𝒰 : X₀.OrderedAffineCover,
      ∀ (i : 𝒰.ι) (V : X₀.Opens), IsAffineOpen V → V ≤ 𝒰.U i →
        ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of S)) (g : (V : Scheme.{u}) ⟶ Y),
          IsAffine Y ∧ Smooth q ∧ IsPullback g (V.ι ≫ f₀) q (Spec.map (CommRingCat.ofHom p)) := by sorry
