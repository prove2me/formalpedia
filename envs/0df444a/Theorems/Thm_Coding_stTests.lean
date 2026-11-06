-- Prove2me | Theorems.Thm_Coding_stTests
-- name    : Coding.stTests
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:04:28.146244+00:00
-- url     : https://prove2.me/theorems/f829abb0-0bea-4007-8977-e8a84b23836c
-- title:
--   Coding: st Tests
-- statement:
--   «An occurrence lies in at most two tests. The total number of tests is the number of occurrences
--   minus the number of variables that occur, hence at most 3m − 1» (Section 6).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccTests.lean#L124-L154
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccTests.lean#L124-L154

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_OccMore
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_Eight_SecProof_Network
import Definitions.Def_Coding_OccTests
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.SatNet Eight
variable {Φ : Fml}

theorem Coding.stTests : StTests := by sorry
