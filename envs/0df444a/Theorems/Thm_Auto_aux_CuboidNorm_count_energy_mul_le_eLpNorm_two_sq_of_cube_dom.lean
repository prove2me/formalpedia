-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_count_energy_mul_le_eLpNorm_two_sq_of_cube_dom
-- name    : Auto.aux_CuboidNorm.count_energy_mul_le_eLpNorm_two_sq_of_cube_dom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:42:30.423775+00:00
-- url     : https://prove2.me/theorems/3514b50f-e057-4ebc-98f0-09774ee62508
-- title:
--   aux Cuboid Norm: count energy mul le e Lp Norm two sq of cube dom
-- statement:
--   The aux Cuboid Norm construction uses the count energy mul le e Lp Norm two sq of cube dom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1847-L1859
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1847-L1859

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

theorem Auto.aux_CuboidNorm.count_energy_mul_le_eLpNorm_two_sq_of_cube_dom {n : ℕ}
    {ε c : ℝ} (hε : ε ≤ 1) (A : Finset (ZVector n))
    (a : ZVector n → ℝ) (G : RVector n → ℝ)
    (hsupport : ∀ k, k ∉ A → c * a k = 0)
    (hdom : ∀ k, k ∈ A → ∀ x, x ∈ latticeCuboid ε k →
      ‖c * a k‖ₑ ≤ ‖G x‖ₑ) :
    (∫⁻ k, ‖c * a k‖ₑ ^ (2 : ℝ) ∂Measure.count) *
        ∏ _ : Fin n, ENNReal.ofReal ε ≤
      eLpNorm G (2 : ℝ≥0∞) volume ^ (2 : ℕ) := by sorry
