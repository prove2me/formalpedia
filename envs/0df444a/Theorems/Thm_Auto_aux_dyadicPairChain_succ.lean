-- Prove2me | Theorems.Thm_Auto_aux_dyadicPairChain_succ
-- name    : Auto.aux_dyadicPairChain_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:38:58.067071+00:00
-- url     : https://prove2.me/theorems/a747fb7a-90a1-4698-8892-65cbfb752026
-- title:
--   Auto: aux dyadic Pair Chain succ
-- statement:
--   Evaluate the padded dyadic pair chain away from its initial point.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L173-L176
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L173-L176

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_dyadicPairChain_succ {J : ℕ} {k : ℤ}
    (x : aux_dyadicInterval k) (j : Fin J) :
    aux_dyadicPairChain J k x j.succ = x := by sorry
