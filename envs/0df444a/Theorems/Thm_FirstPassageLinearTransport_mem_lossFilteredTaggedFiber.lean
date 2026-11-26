-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
-- name    : FirstPassageLinearTransport.mem_lossFilteredTaggedFiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:00:21.85806+00:00
-- url     : https://prove2.me/theorems/4a2ec73c-23f2-5171-8a6f-ed6436729380
-- title:
--   First Passage Linear Transport: mem loss Filtered Tagged Fiber
-- statement:
--   The First Passage Linear Transport construction uses the mem loss Filtered Tagged Fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/LossTransport.lean#L71-L77
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/LossTransport.lean#L71-L77

import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_LossTransport
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.mem_lossFilteredTaggedFiber
    {M Y h y n : ℕ} {D : ℚ} :
    n ∈ lossFilteredTaggedFiber M Y h y D ↔
      n ∈ dyadicShell M ∧ IsFirstPassage Y n h ∧ orbit h n = y ∧
        scaledReverseLoss Y n h ≤ D := by sorry
