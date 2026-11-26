-- Prove2me | Theorems.Thm_Auto_aux_log_weight_conversion_Ioc
-- name    : Auto.aux_log_weight_conversion_Ioc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:40:32.325548+00:00
-- url     : https://prove2.me/theorems/5d5836a3-5a72-4189-bb4d-59cf59df472a
-- title:
--   Auto: aux log weight conversion Ioc
-- statement:
--   Convert the ordinary product integral on an `Ioc` interval to its
--   logarithmically weighted form.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L1001-L1019
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L1001-L1019

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_log_weight_conversion_Ioc {α β x y : ℝ} (hx : 0 < x)
    (hsub : Set.Ioc x y ⊆ Set.Icc α β) (a d : ℝ → ℝ) :
    ∫⁻ z in Set.Ioc x y, ‖a z‖ₑ * ‖d z‖ₑ =
      ∫⁻ z in Set.Ioc x y, ‖a z‖ₑ * ‖z * d z‖ₑ
        ∂aux_logarithmicMeasure α β := by sorry
