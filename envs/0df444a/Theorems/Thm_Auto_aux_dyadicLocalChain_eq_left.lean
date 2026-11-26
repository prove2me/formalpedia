-- Prove2me | Theorems.Thm_Auto_aux_dyadicLocalChain_eq_left
-- name    : Auto.aux_dyadicLocalChain_eq_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:38:45.3718+00:00
-- url     : https://prove2.me/theorems/1d833ab5-965c-59ed-88a9-b4546135527a
-- title:
--   Auto: aux dyadic Local Chain eq left
-- statement:
--   A clamped point before a dyadic interval becomes its left endpoint.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L119-L123
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L119-L123

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_dyadicLocalChain_eq_left {J : ℕ} {k : ℤ}
    {t : Fin (J + 1) → ℝ} {j : Fin (J + 1)} (hj : t j ≤ (2 : ℝ) ^ k) :
    (aux_dyadicLocalChain J k t j : ℝ) = (2 : ℝ) ^ k := by sorry
