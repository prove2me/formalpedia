-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_rankWeight_div
-- name    : FirstPassageLinearTransport.rankWeight_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:16:00.640348+00:00
-- url     : https://prove2.me/theorems/81f5f133-4ce8-4eba-8fad-beaacfd99d81
-- title:
--   First Passage Linear Transport: rank Weight div
-- statement:
--   The First Passage Linear Transport construction uses the rank Weight div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RankScaledLoss.lean#L34-L51
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RankScaledLoss.lean#L34-L51

import Definitions.Def_FirstPassageLinearTransport_NestedRecertification
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.rankWeight_div (q d : ℕ) :
    ((q + (d + 1) + 2 : ℕ) : ℚ) / (2 : ℚ) ^ (d + 1) ≤
      ((q + 3 : ℕ) : ℚ) / 2 := by sorry
