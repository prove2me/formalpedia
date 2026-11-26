-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_count_energy_mul_le_lintegral_of_cube_dom
-- name    : Auto.aux_CuboidNorm.count_energy_mul_le_lintegral_of_cube_dom
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T17:42:26.3821+00:00
-- url     : https://prove2.me/theorems/6521b157-2e4b-4fba-8a6a-9a29ea199f92
-- title:
--   aux Cuboid Norm: count energy mul le lintegral of cube dom
-- statement:
--   The aux Cuboid Norm construction uses the count energy mul le lintegral of cube dom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1822-L1836
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1822-L1836

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
open Auto.aux_CuboidNorm
variable {α κ : Type*} [MeasurableSpace α] [DecidableEq κ]

theorem Auto.aux_CuboidNorm.count_energy_mul_le_lintegral_of_cube_dom {n : ℕ}
    {ε c : ℝ} (hε : ε ≤ 1) (A : Finset (ZVector n))
    (a : ZVector n → ℝ) (G : RVector n → ℝ)
    (hsupport : ∀ k, k ∉ A → c * a k = 0)
    (hdom : ∀ k, k ∈ A → ∀ x, x ∈ latticeCuboid ε k →
      ‖c * a k‖ₑ ≤ ‖G x‖ₑ) :
    (∫⁻ k, ‖c * a k‖ₑ ^ (2 : ℝ) ∂Measure.count) *
        ∏ _ : Fin n, ENNReal.ofReal ε ≤
      ∫⁻ x, ‖G x‖ₑ ^ (2 : ℝ) ∂volume := by sorry
