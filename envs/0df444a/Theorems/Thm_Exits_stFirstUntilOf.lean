-- Prove2me | Theorems.Thm_Exits_stFirstUntilOf
-- name    : Exits.stFirstUntilOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:53:45.281535+00:00
-- url     : https://prove2.me/theorems/1a3938d6-11b5-47d9-bf05-eccb67a1dc2d
-- title:
--   Exits: st First Until Of
-- statement:
--   «try all groupings into K_ℓ groups until one is good» (line 10 of Algorithm 1), from the loop:
--   the points met are (a, y) for y below `reach`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Runs.lean#L114-L147
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Runs.lean#L114-L147

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

theorem Exits.stFirstUntilOf : StFirstUntilOf := by sorry
