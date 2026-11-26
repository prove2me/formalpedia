-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_log_two_eq_of_mem_dyadicShell
-- name    : FirstPassageLinearTransport.log_two_eq_of_mem_dyadicShell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:03:58.767167+00:00
-- url     : https://prove2.me/theorems/cbc5a67c-5a4a-42d3-b605-b2199f0c79b0
-- title:
--   First Passage Linear Transport: log two eq of mem dyadic Shell
-- statement:
--   The First Passage Linear Transport construction uses the log two eq of mem dyadic Shell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/BarrierDensity.lean#L38-L41
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/BarrierDensity.lean#L38-L41

import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.log_two_eq_of_mem_dyadicShell {M n : ℕ}
    (hn : n ∈ dyadicShell M) : Nat.log 2 n = M := by sorry
