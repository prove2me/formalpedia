-- Prove2me | Theorems.Thm_Auto_aux_cross_square_le
-- name    : Auto.aux_cross_square_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:40:06.300115+00:00
-- url     : https://prove2.me/theorems/df8175d4-f657-56e9-927f-8ca7edcb0196
-- title:
--   Auto: aux cross square le
-- statement:
--   A coarse algebraic estimate used when an interval crosses a zero of the
--   function.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L889-L899
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L889-L899

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_cross_square_le (u v : ℝ) :
    ‖u - v‖ₑ ^ (2 : ℕ) ≤
      2 * (‖u * u‖ₑ + ‖v * v‖ₑ) := by sorry
