-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSources
-- name    : FirstPassageLinearTransport.mem_lossFilteredTransportedSources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:00:32.802273+00:00
-- url     : https://prove2.me/theorems/7abb523c-826e-5acc-8de2-b8694fa43649
-- title:
--   First Passage Linear Transport: mem loss Filtered Transported Sources
-- statement:
--   The First Passage Linear Transport construction uses the mem loss Filtered Transported Sources property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/LossTransport.lean#L254-L280
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/LossTransport.lean#L254-L280

import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_LossTransport
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.mem_lossFilteredTransportedSources
    {M Y H n : ℕ} {B : Finset ℕ} {D : ℚ} :
    n ∈ lossFilteredTransportedSources M Y H B D ↔
      n ∈ dyadicShell M ∧
        ∃ h : ℕ, 1 ≤ h ∧ h ≤ H ∧ IsFirstPassage Y n h ∧
          orbit h n ∈ B ∧ scaledReverseLoss Y n h ≤ D := by sorry
