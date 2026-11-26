-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_maximalBarrier_phase_two
-- name    : FirstPassageLinearTransport.maximalBarrier_phase_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:06:00.932837+00:00
-- url     : https://prove2.me/theorems/918e1536-8089-4f27-9992-65714ebe0e49
-- title:
--   First Passage Linear Transport: maximal Barrier phase two
-- statement:
--   The First Passage Linear Transport construction uses the maximal Barrier phase two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L380-L405
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L380-L405

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section

theorem FirstPassageLinearTransport.maximalBarrier_phase_two {n M : ℕ} {t : ℝ}
    (ht : 0 < t) (hstart : 2 ≤ t * M)
    (hnShell : n ∈ dyadicShell M) :
    2 * (3 : ℝ) ^ maximalBarrierHeight t M ≤ (n : ℝ) ^ t := by sorry
