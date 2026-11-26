-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSourcesAtTimes
-- name    : FirstPassageLinearTransport.mem_lossFilteredTransportedSourcesAtTimes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:02:19.870849+00:00
-- url     : https://prove2.me/theorems/8f2a6336-ffaa-442f-9ef6-a2b04f91678f
-- title:
--   First Passage Linear Transport: mem loss Filtered Transported Sources At Times
-- statement:
--   The First Passage Linear Transport construction uses the mem loss Filtered Transported Sources At Times property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeSupportTransport.lean#L30-L51
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeSupportTransport.lean#L30-L51

import Definitions.Def_FirstPassageLinearTransport_LossTransport
import Definitions.Def_FirstPassageLinearTransport_TimeSupportTransport
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.mem_lossFilteredTransportedSourcesAtTimes
    {M Y n : ℕ} {times B : Finset ℕ} {D : ℚ} :
    n ∈ lossFilteredTransportedSourcesAtTimes M Y times B D ↔
      n ∈ dyadicShell M ∧
        ∃ h : ℕ, h ∈ times ∧ IsFirstPassage Y n h ∧
          orbit h n ∈ B ∧ scaledReverseLoss Y n h ≤ D := by sorry
