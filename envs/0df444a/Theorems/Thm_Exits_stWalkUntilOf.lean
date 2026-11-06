-- Prove2me | Theorems.Thm_Exits_stWalkUntilOf
-- name    : Exits.stWalkUntilOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:53:58.986198+00:00
-- url     : https://prove2.me/theorems/07f74e81-5920-4232-b328-e68846d31bfe
-- title:
--   Exits: st Walk Until Of
-- statement:
--   «for each … do» (line 2 of Algorithm 1), run so that it stops at the first Φ with Count(Φ) > 0
--   (the deciding form), from the loop: the stacks met are those up to the first whose top is a leaf
--   that passes.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Runs.lean#L189-L222
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Runs.lean#L189-L222

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

theorem Exits.stWalkUntilOf : StWalkUntilOf := by sorry
