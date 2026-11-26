-- Prove2me | Theorems.Thm_Auto_aux_dyadicPairChain_mono
-- name    : Auto.aux_dyadicPairChain_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:38:48.931626+00:00
-- url     : https://prove2.me/theorems/270a816f-6b6a-5072-9a21-cba2ae2eee35
-- title:
--   Auto: aux dyadic Pair Chain mono
-- statement:
--   The padded dyadic pair chain is monotone.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L150-L165
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L150-L165

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_dyadicPairChain_mono {J : ℕ} {k : ℤ} (x : aux_dyadicInterval k) :
    Monotone (aux_dyadicPairChain J k x) := by sorry
