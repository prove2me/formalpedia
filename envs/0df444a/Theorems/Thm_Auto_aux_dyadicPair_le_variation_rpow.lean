-- Prove2me | Theorems.Thm_Auto_aux_dyadicPair_le_variation_rpow
-- name    : Auto.aux_dyadicPair_le_variation_rpow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:38:55.732627+00:00
-- url     : https://prove2.me/theorems/f20f7e57-23f2-52b8-84f5-5bea473dcbb9
-- title:
--   Auto: aux dyadic Pair le variation rpow
-- statement:
--   A dyadic lower-endpoint tail is bounded by the corresponding local
--   variation whenever there is at least one available jump.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L196-L214
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L196-L214

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_dyadicPair_le_variation_rpow {B : Type*} [SeminormedAddCommGroup B]
    {J : ℕ} (hJ : 0 < J) {k : ℤ} (a : ℝ → B) (r : ℝ) (hr : 1 ≤ r)
    (x : aux_dyadicInterval k) :
    (‖a x - a ((2 : ℝ) ^ k)‖₊ : ℝ≥0∞) ^ r ≤
      (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r := by sorry
