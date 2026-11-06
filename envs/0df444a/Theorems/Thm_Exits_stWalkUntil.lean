-- Prove2me | Theorems.Thm_Exits_stWalkUntil
-- name    : Exits.stWalkUntil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:54:19.541566+00:00
-- url     : https://prove2.me/theorems/5b49d9c3-0403-4113-b99f-ec4dcfeb8fc8
-- title:
--   Exits: st Walk Until
-- statement:
--   «for each … do» (line 2 of Algorithm 1), run so that it stops at the first Φ with Count(Φ) > 0
--   (the deciding form): the walk halts at the first leaf that passes, within t + 2 steps for each leaf
--   tested and k more.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Runs.lean#L227-L227
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Runs.lean#L227-L227

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

theorem Exits.stWalkUntil : StWalkUntil := by sorry
