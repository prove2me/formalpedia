-- Prove2me | Theorems.Thm_Auto_aux_log_holder_lintegral
-- name    : Auto.aux_log_holder_lintegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:40:20.599894+00:00
-- url     : https://prove2.me/theorems/deb09011-8533-57dc-a19a-010f57f772cf
-- title:
--   Auto: aux log holder lintegral
-- statement:
--   Global logarithmic `L²` Hölder estimate.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L1022-L1039
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L1022-L1039

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_log_holder_lintegral {α β : ℝ} (a : ℝ → ℝ)
    (ha : ContDiffOn ℝ 1 a (Set.Icc α β)) :
    ∫⁻ z, ‖a z‖ₑ * ‖z * deriv a z‖ₑ ∂aux_logarithmicMeasure α β ≤
      aux_logarithmicL2 α β a *
        aux_logarithmicL2 α β (fun z ↦ z * deriv a z) := by sorry
