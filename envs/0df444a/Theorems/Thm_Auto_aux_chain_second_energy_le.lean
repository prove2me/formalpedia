-- Prove2me | Theorems.Thm_Auto_aux_chain_second_energy_le
-- name    : Auto.aux_chain_second_energy_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:40:36.089968+00:00
-- url     : https://prove2.me/theorems/133c640c-feb1-4fdf-bf5e-267539919f15
-- title:
--   Auto: aux chain second energy le
-- statement:
--   The second FTC estimate summed over one monotone chain.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L1051-L1097
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L1051-L1097

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_chain_second_energy_le {J : ℕ} {α β : ℝ} (hα : 0 < α)
    (a : ℝ → ℝ) (ha : ContDiffOn ℝ 1 a (Set.Icc α β))
    (t : Fin (J + 1) → Set.Icc α β) (ht : Monotone t) :
    (∑ j : Fin J,
      ((‖a (t j.succ) - a (t j.castSucc)‖₊ : ℝ≥0∞) ^ (2 : ℝ))) ≤
      8 * aux_logarithmicL2 α β a *
        aux_logarithmicL2 α β (fun z ↦ z * deriv a z) := by sorry
