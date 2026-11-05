-- Prove2me | Theorems.Thm_Exits_stFoldUntil
-- name    : Exits.stFoldUntil
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T16:51:29.177981+00:00
-- url     : https://prove2.me/theorems/e8f66bb8-a754-4e84-96a4-d5ce7d1d3773
-- title:
--   Exits: st Fold Until
-- statement:
--   **The loop that can be left.** Steps: Σ (steps of the body + 1) over the points that are met;
--   result: the fold over them. Behind «until one is good» (line 10 of Algorithm 1) and the stop at the
--   first Φ with Count(Φ) > 0 in the deciding form of lines 2 and 3.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Runs.lean#L106-L108
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Runs.lean#L106-L108

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

theorem Exits.stFoldUntil : StFoldUntil := by sorry
