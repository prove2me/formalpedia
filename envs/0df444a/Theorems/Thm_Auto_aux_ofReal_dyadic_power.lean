-- Prove2me | Theorems.Thm_Auto_aux_ofReal_dyadic_power
-- name    : Auto.aux_ofReal_dyadic_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:43:26.858402+00:00
-- url     : https://prove2.me/theorems/72ff8466-5541-4f57-9c15-7772ab5ef874
-- title:
--   Auto: aux of Real dyadic power
-- statement:
--   The Auto construction uses the aux of Real dyadic power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2277-L2280
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2277-L2280

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section

theorem Auto.aux_ofReal_dyadic_power (n : ℕ) :
    ENNReal.ofReal ((2 : ℝ) ^ (3 * n + 6)) =
      ((2 : ℝ≥0∞) ^ (3 * n + 6)) := by sorry
