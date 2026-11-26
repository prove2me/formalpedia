-- Prove2me | Theorems.Thm_Auto_aux_dyadicPairChain_zero
-- name    : Auto.aux_dyadicPairChain_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:39:01.139681+00:00
-- url     : https://prove2.me/theorems/de47d70f-3950-5c3f-b85e-03161c0d2ab8
-- title:
--   Auto: aux dyadic Pair Chain zero
-- statement:
--   Evaluate the padded dyadic pair chain at its initial point.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L168-L170
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L168-L170

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_dyadicPairChain_zero {J : ℕ} {k : ℤ} (x : aux_dyadicInterval k) :
    aux_dyadicPairChain J k x 0 = aux_dyadicLowerPoint k := by sorry
