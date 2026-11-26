-- Prove2me | Theorems.Thm_Auto_aux_dyadicLocalChain_eq_of_mem
-- name    : Auto.aux_dyadicLocalChain_eq_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:38:23.134729+00:00
-- url     : https://prove2.me/theorems/baf4b1bc-99bc-5276-ac1b-769c499abcde
-- title:
--   Auto: aux dyadic Local Chain eq of mem
-- statement:
--   A clamped point already inside its dyadic interval is unchanged.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L111-L116
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L111-L116

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_dyadicLocalChain_eq_of_mem {J : ℕ} {k : ℤ}
    {t : Fin (J + 1) → ℝ} {j : Fin (J + 1)}
    (hj : t j ∈ Set.Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))) :
    (aux_dyadicLocalChain J k t j : ℝ) = t j := by sorry
