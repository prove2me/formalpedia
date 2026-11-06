-- Prove2me | Theorems.Thm_Coding_toFinset_tests
-- name    : Coding.toFinset_tests
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:05:44.977535+00:00
-- url     : https://prove2.me/theorems/06305b2e-164e-4879-83e2-317322f209a4
-- title:
--   Coding: to Finset tests
-- statement:
--   The tests are the pairs of the links of Lean's network, taken slot by slot.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccTests.lean#L73-L84
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccTests.lean#L73-L84

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_OccMore
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_Eight_SecProof_Network
import Definitions.Def_Coding_OccTests
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.SatNet Eight
variable {Φ : Fml}

theorem Coding.toFinset_tests (h3 : ∀ C ∈ Φ, C.length ≤ 3) : (tests Φ).toFinset = (testsOf Φ 1 Φ.length 3).image fun t => (occOfSlot t.1, occOfSlot t.2) := by sorry
