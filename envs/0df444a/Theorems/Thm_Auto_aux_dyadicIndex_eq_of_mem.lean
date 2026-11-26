-- Prove2me | Theorems.Thm_Auto_aux_dyadicIndex_eq_of_mem
-- name    : Auto.aux_dyadicIndex_eq_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:39:13.184898+00:00
-- url     : https://prove2.me/theorems/03ea9eba-603b-5d9a-9c92-9a4ea017a853
-- title:
--   Auto: aux dyadic Index eq of mem
-- statement:
--   The dyadic interval label is unique.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L248-L262
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L248-L262

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_dyadicIndex_eq_of_mem {x : ℝ} {k : ℤ} (hx : 0 < x)
    (hk : (2 : ℝ) ^ k ≤ x ∧ x < (2 : ℝ) ^ (k + 1)) : aux_dyadicIndex x = k := by sorry
