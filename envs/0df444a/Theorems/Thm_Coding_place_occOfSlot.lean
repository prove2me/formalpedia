-- Prove2me | Theorems.Thm_Coding_place_occOfSlot
-- name    : Coding.place_occOfSlot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:06:49.165356+00:00
-- url     : https://prove2.me/theorems/50abfe75-d019-45ca-a0ad-d9ad106b503d
-- title:
--   Coding: place occ Of Slot
-- statement:
--   The place of the pair of a slot is the index that Lean's network gives the slot.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccTests.lean#L36-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccTests.lean#L36-L38

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

theorem Coding.place_occOfSlot {m : ℕ} (p : Slot 1 m 3) : place (occOfSlot p) = idx p := by sorry
