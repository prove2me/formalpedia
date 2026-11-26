-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_mem_landingBad
-- name    : FirstPassageLinearTransport.mem_landingBad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:06:16.115734+00:00
-- url     : https://prove2.me/theorems/58db2306-2d12-4561-9763-d3c9b583f93f
-- title:
--   First Passage Linear Transport: mem landing Bad
-- statement:
--   The First Passage Linear Transport construction uses the mem landing Bad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstBadEnvelope.lean#L33-L37
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstBadEnvelope.lean#L33-L37

import Definitions.Def_FirstPassageLinearTransport_AdjustableBarrierDensity
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_FirstBadEnvelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.mem_landingBad {q y : ℕ} {t : ℝ} :
    y ∈ landingBad q t ↔
      2 ^ (q - 1) < y ∧ y ≤ 2 ^ q ∧ y ∉ initialWindowGood t := by sorry
