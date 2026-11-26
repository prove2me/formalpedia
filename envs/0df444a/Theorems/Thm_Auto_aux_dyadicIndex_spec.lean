-- Prove2me | Theorems.Thm_Auto_aux_dyadicIndex_spec
-- name    : Auto.aux_dyadicIndex_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:38:17.556081+00:00
-- url     : https://prove2.me/theorems/31112745-d494-5661-a725-dacfbf7ff465
-- title:
--   Auto: aux dyadic Index spec
-- statement:
--   A positive point belongs to the dyadic interval indexed by
--   `aux_dyadicIndex`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L229-L233
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L229-L233

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_dyadicIndex_spec (x : ℝ) (hx : 0 < x) :
    (2 : ℝ) ^ aux_dyadicIndex x ≤ x ∧ x < (2 : ℝ) ^ (aux_dyadicIndex x + 1) := by sorry
