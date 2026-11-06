-- Prove2me | Theorems.Thm_Exits_length_tested_visits
-- name    : Exits.length_tested_visits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:45:48.450401+00:00
-- url     : https://prove2.me/theorems/3b6727cd-42c2-4281-a50e-96fe124855ef
-- title:
--   Exits: length tested visits
-- statement:
--   **How many stacks are met.** While the tree below s, of depth at most k, is walked up to the
--   first leaf that passes, at most 2·(number of leaves tested) + k − 1 stacks are met: an inner node
--   that is met either has all the leaves of its left half tested, or lies on the path to the last leaf
--   tested.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Runs.lean#L159-L184
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Runs.lean#L159-L184

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

theorem Exits.length_tested_visits (step : ν → Option (ν × ν)) (v : ν → Bool) (w : List ν → Bool) (hw : ∀ st, w st = ((walkSel step st).map v).getD false) (k : ℕ) (s : ν) (r : List ν)
    (hk : ∀ x ∈ leaves step k s, step x = none) : (tested w (visits step k s r)).length + 1 ≤ 2 * (tested v (leaves step k s)).length + k := by sorry
