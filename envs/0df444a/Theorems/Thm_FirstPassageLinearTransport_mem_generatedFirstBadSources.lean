-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_mem_generatedFirstBadSources
-- name    : FirstPassageLinearTransport.mem_generatedFirstBadSources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:05:59.888712+00:00
-- url     : https://prove2.me/theorems/5bf5ebf7-8844-5230-9b27-708ca3171df0
-- title:
--   First Passage Linear Transport: mem generated First Bad Sources
-- statement:
--   The First Passage Linear Transport construction uses the mem generated First Bad Sources property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstBadEnvelope.lean#L182-L187
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstBadEnvelope.lean#L182-L187

import Definitions.Def_FirstPassageLinearTransport_AdjustableBarrierDensity
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_FirstBadEnvelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.mem_generatedFirstBadSources
    {M L U H n : ℕ} {r : ℚ} {t : ℝ} :
    n ∈ generatedFirstBadSources M L U H r t ↔
      n ∈ dyadicShell M ∧ HasGeneratedFirstBadLanding r t n L U H := by sorry
