-- Prove2me | Theorems.Thm_Eight_ViaGrouping_stAlg_from
-- name    : Eight.ViaGrouping.stAlg_from
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:52:30.5127+00:00
-- url     : https://prove2.me/theorems/d5b555c8-b56c-4a99-978d-c716b9c99315
-- title:
--   Via Grouping: st Alg from
-- statement:
--   The interface statement `CircuitLowerBound.StAlg`, from Corollary 6 for machines cut into steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/CorENP.lean#L52-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/CorENP.lean#L52-L52

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_ENP
import Definitions.Def_Eight_ViaGrouping_CorDefs2
import Definitions.Def_Eight_ViaGrouping_CorGraph
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_CorENP
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open ENP Groundwork Turing CircuitLowerBound

theorem Eight.ViaGrouping.stAlg_from (hEng : StEngine) : StAlg := by sorry
