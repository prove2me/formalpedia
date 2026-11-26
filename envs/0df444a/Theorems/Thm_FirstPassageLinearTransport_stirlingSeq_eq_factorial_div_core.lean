-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stirlingSeq_eq_factorial_div_core
-- name    : FirstPassageLinearTransport.stirlingSeq_eq_factorial_div_core
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:20:46.910851+00:00
-- url     : https://prove2.me/theorems/445f272d-10eb-4a0e-baf7-41a64b098b93
-- title:
--   First Passage Linear Transport: stirling Seq eq factorial div core
-- statement:
--   The First Passage Linear Transport construction uses the stirling Seq eq factorial div core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpEntropyBarrier.lean#L386-L388
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpEntropyBarrier.lean#L386-L388

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

theorem FirstPassageLinearTransport.stirlingSeq_eq_factorial_div_core (n : ℕ) :
    Stirling.stirlingSeq n = (Nat.factorial n : ℝ) / stirlingCore n := by sorry
