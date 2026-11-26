-- Prove2me | Theorems.Thm_Auto_aux_enorm_mul_inv_cancel
-- name    : Auto.aux_enorm_mul_inv_cancel
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:40:12.550415+00:00
-- url     : https://prove2.me/theorems/a1d3292c-dc35-5c25-9712-cd087d9e94ca
-- title:
--   Auto: aux enorm mul inv cancel
-- statement:
--   Cancellation of the logarithmic density on an `Ioc` interval.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L983-L987
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L983-L987

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_enorm_mul_inv_cancel {z d : ℝ} (hz : 0 < z) :
    ENNReal.ofReal z⁻¹ * ‖z * d‖ₑ = ‖d‖ₑ := by sorry
