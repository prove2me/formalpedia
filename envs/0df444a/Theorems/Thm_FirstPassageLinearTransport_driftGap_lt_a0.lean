-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_driftGap_lt_a0
-- name    : FirstPassageLinearTransport.driftGap_lt_a0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:14:54.777994+00:00
-- url     : https://prove2.me/theorems/55c78343-f252-4e77-b0e7-a0e6bf4fc3df
-- title:
--   First Passage Linear Transport: drift Gap lt a0
-- statement:
--   The First Passage Linear Transport construction uses the drift Gap lt a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FixedPolylogParameters.lean#L46-L51
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FixedPolylogParameters.lean#L46-L51

import Definitions.Def_FirstPassageLinearTransport_AdjustableEntropyRate
import Definitions.Def_FirstPassageLinearTransport_Constants
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.driftGap_lt_a0 : driftGap < a0 := by sorry
