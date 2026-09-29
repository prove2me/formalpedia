-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_refinement_preimage_preimage_of_isSeparated
-- name    : AlgebraicGeometry.Scheme.OrderedAffineCover.exists_refinement_preimage_preimage_of_isSeparated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/afff651c-3132-55b6-907f-a32840e10041
-- title:
--   Common affine refinement of two pulled-back ordered affine covers
-- statement:
--   Let $R$ be a commutative ring, let $X$ be a scheme (in universe $0$), and let $f : X \to \operatorname{Spec} R$ be a separated morphism. Let $\mathcal{K}$ be an ordered affine cover of $X$, that is: a finite linearly ordered index type $\mathcal{K}.\iota$ together with a family $U_a$ of open subschemes of $X$, each an affine open, with $\bigsqcup_a U_a = \top$. Let $h_1, h_2 : X \to X$ be two affine morphisms from $X$ to itself. The assertion is that there exist an ordered affine cover $\mathcal{W}$ of $X$ (again a finite linearly ordered index set, a family of affine opens $W_w$, covering $X$) and two index maps $\lambda_1, \lambda_2 : \mathcal{W}.\iota \to \mathcal{K}.\iota$ such that for every $w$ one has $W_w \le h_1^{-1} U_{\lambda_1 w}$ and $W_w \le h_2^{-1} U_{\lambda_2 w}$ as opens of $X$; that is, $\mathcal{W}$ simultaneously refines the two pulled-back covers $(h_1^{-1}U_a)_a$ and $(h_2^{-1}U_a)_a$, with explicit index maps recording the refinement.
--
--   This is the standard construction of a common refinement of two covers obtained by pulling back a finite affine cover along affine self-maps, using that on a scheme separated over an affine base the intersection of two affine opens is affine. It supplies the refinement data $(\mathcal{W},\lambda_1,\lambda_2)$ used in the Čech-cocycle manipulations behind the descent statements [`GoodReductionJacobian.AbelianSchemePropertyBundle.nonempty_iso_of_pullback_iso_of_sliceAt_one_of_isPullback_of_ker_mul_self_of_isNoetherianRing`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.nonempty_iso_of_pullback_iso_of_sliceAt_one_of_isPullback_of_ker_mul_self_of_isNoetherianRing) and [`GoodReductionJacobian.AbelianSchemePropertyBundle.nonempty_iso_unit_of_pullback_iso_unit_of_isSymmetric_of_ker_mul_maximalIdeal_of_isUnit_two_of_isNoetherianRing`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.nonempty_iso_unit_of_pullback_iso_unit_of_isSymmetric_of_ker_mul_maximalIdeal_of_isUnit_two_of_isNoetherianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_refinement_preimage_preimage_of_isSeparated.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.OrderedAffineCover.exists_refinement_preimage_preimage_of_isSeparated
    {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) [IsSeparated f]
    (𝒦 : X.OrderedAffineCover) (h₁ h₂ : X ⟶ X) [IsAffineHom h₁] [IsAffineHom h₂] :
    ∃ (𝒲 : X.OrderedAffineCover) (lam₁ lam₂ : 𝒲.ι → 𝒦.ι),
      (∀ w, 𝒲.U w ≤ h₁ ⁻¹ᵁ 𝒦.U (lam₁ w)) ∧ (∀ w, 𝒲.U w ≤ h₂ ⁻¹ᵁ 𝒦.U (lam₂ w)) := by sorry
