-- Prove2me | Theorems.Thm_Coding_occOfSlot_injective
-- name    : Coding.occOfSlot_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:06:37.067295+00:00
-- url     : https://prove2.me/theorems/f3c0df42-dc28-48ba-84b2-0e2f0158b1d2
-- title:
--   Coding: occ Of Slot injective
-- statement:
--   Different slots have different pairs.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccTests.lean#L41-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccTests.lean#L41-L42

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

theorem Coding.occOfSlot_injective {m : ℕ} : Function.Injective (occOfSlot (m := m)) := by sorry
