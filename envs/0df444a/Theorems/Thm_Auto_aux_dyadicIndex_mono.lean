-- Prove2me | Theorems.Thm_Auto_aux_dyadicIndex_mono
-- name    : Auto.aux_dyadicIndex_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:39:21.438082+00:00
-- url     : https://prove2.me/theorems/eb9d7463-cce5-4749-b24f-805b01dd6e9f
-- title:
--   Auto: aux dyadic Index mono
-- statement:
--   Dyadic interval indices respect the order on positive reals.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L236-L245
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L236-L245

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_dyadicIndex_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    aux_dyadicIndex x ≤ aux_dyadicIndex y := by sorry
