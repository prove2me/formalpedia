-- Prove2me | Theorems.Thm_Eight_ViaGrouping_verifier_polyTimeSteps
-- name    : Eight.ViaGrouping.verifier_polyTimeSteps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:38:57.463103+00:00
-- url     : https://prove2.me/theorems/a1f5b509-e270-4f6f-801b-30741ba27d9e
-- title:
--   Via Grouping: verifier poly Time Steps
-- statement:
--   The verifier has polynomial-time steps if M has.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/CorNSETH.lean#L41-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/CorNSETH.lean#L41-L44

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_NSETH
import Definitions.Def_Eight_ViaGrouping_CorDefs2
import Definitions.Def_GraphProblems_Host
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_CorNSETH
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Paper Turing

theorem Eight.ViaGrouping.verifier_polyTimeSteps {M : StepMachine (List Bool) Bool} (hp : PolyTimeSteps M) : PolyTimeSteps (verifier M) := by sorry
