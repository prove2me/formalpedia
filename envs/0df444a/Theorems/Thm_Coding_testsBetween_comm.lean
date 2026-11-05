-- Prove2me | Theorems.Thm_Coding_testsBetween_comm
-- name    : Coding.testsBetween_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:05:44.84136+00:00
-- url     : https://prove2.me/theorems/64f66318-3577-46fa-adad-1250a59eb6a7
-- title:
--   Coding: tests Between comm
-- statement:
--   The tests between the clusters a and b do not depend on the order in which the clusters are
--   named.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLinks.lean#L64-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLinks.lean#L64-L64

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_OccLists
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Mathlib.Tactic.Ring
import Definitions.Def_Coding_OccLinks
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Coding
open Groundwork Groundwork.Prog Groundwork.Prog.Count
variable {g : ℕ} {Φ : Fml}

theorem Coding.testsBetween_comm (a b : ℕ) : testsBetween g Φ a b = testsBetween g Φ b a := by sorry
