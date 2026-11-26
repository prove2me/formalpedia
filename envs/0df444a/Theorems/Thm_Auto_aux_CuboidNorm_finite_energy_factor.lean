-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_finite_energy_factor
-- name    : Auto.aux_CuboidNorm.finite_energy_factor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:42:19.89011+00:00
-- url     : https://prove2.me/theorems/046de86b-8e24-5b2d-921d-9f9c2949270b
-- title:
--   aux Cuboid Norm: finite energy factor
-- statement:
--   The aux Cuboid Norm construction uses the finite energy factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1909-L1926
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1909-L1926

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

theorem Auto.aux_CuboidNorm.finite_energy_factor {n : ℕ} (A : Finset (ZVector n))
    (ε c : ℝ) (hc : 0 ≤ c) (a : ZVector n → ℝ) :
    (∑ k ∈ A, ‖c * a k‖ₑ ^ (2 : ℝ)) *
        ∏ _ : Fin n, ENNReal.ofReal ε =
      (ENNReal.ofReal c ^ (2 : ℝ) * ENNReal.ofReal ε ^ n) *
        ∑ k ∈ A, ‖a k‖ₑ ^ (2 : ℝ) := by sorry
