-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_maximalBarrier_phase_half
-- name    : FirstPassageLinearTransport.maximalBarrier_phase_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:01:16.856675+00:00
-- url     : https://prove2.me/theorems/b59ebeea-6576-4cb1-8ff1-628df34b362f
-- title:
--   First Passage Linear Transport: maximal Barrier phase half
-- statement:
--   The First Passage Linear Transport construction uses the maximal Barrier phase half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L365-L378
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L365-L378

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section

theorem FirstPassageLinearTransport.maximalBarrier_phase_half {n M : ℕ} {t : ℝ}
    (ht : 0 ≤ t) (hnShell : n ∈ dyadicShell M) :
    (3 : ℝ) ^ maximalBarrierHeight t M ≤ (n : ℝ) ^ (t / 2) := by sorry
