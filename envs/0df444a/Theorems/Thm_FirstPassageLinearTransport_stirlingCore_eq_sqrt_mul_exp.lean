-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stirlingCore_eq_sqrt_mul_exp
-- name    : FirstPassageLinearTransport.stirlingCore_eq_sqrt_mul_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:20:30.929186+00:00
-- url     : https://prove2.me/theorems/616ce082-93d7-4188-8177-6e7429544840
-- title:
--   First Passage Linear Transport: stirling Core eq sqrt mul exp
-- statement:
--   The First Passage Linear Transport construction uses the stirling Core eq sqrt mul exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpEntropyBarrier.lean#L231-L245
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpEntropyBarrier.lean#L231-L245

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Nat
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.stirlingCore_eq_sqrt_mul_exp
    {n : ℕ} (hn : 0 < n) :
    stirlingCore n =
      Real.sqrt (2 * n) *
        Real.exp ((n : ℝ) * (Real.log n - 1)) := by sorry
