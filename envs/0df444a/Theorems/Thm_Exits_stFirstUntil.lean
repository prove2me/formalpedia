-- Prove2me | Theorems.Thm_Exits_stFirstUntil
-- name    : Exits.stFirstUntil
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T16:51:39.902741+00:00
-- url     : https://prove2.me/theorems/04e90bf3-19ab-4839-bc30-bb277669f40b
-- title:
--   Exits: st First Until
-- statement:
--   «try all groupings into K_ℓ groups until one is good» (line 10 of Algorithm 1): the search halts
--   at the first good number, within the steps of the numbers up to it.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Runs.lean#L151-L151
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Runs.lean#L151-L151

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_Tested
import Definitions.Def_StepMachines_Prog_Range
import Definitions.Def_StepMachines_Prog_Range
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_Exits_Runs
set_option autoImplicit false
section
section
open Exits
open Finset Groundwork Groundwork.Stepped
open Groundwork.Sparsify (leaves)
variable {α β γ τ ν : Type}

theorem Exits.stFirstUntil : StFirstUntil := by sorry
