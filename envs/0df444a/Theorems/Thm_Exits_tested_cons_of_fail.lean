-- Prove2me | Theorems.Thm_Exits_tested_cons_of_fail
-- name    : Exits.tested_cons_of_fail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:48:10.633215+00:00
-- url     : https://prove2.me/theorems/e78487d0-cd56-4b0e-9b19-ca063a25f139
-- title:
--   Exits: tested cons of fail
-- statement:
--   If the first entry fails, the search goes on behind it.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L38-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L38-L38

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_Defs
import Definitions.Def_Exits_Tested
set_option autoImplicit false
section
section
open Exits
open Groundwork Groundwork.Stepped
variable {α β γ τ ν : Type}

theorem Exits.tested_cons_of_fail {v : ν → Bool} {x : ν} (h : v x = false) (l : List ν) : tested v (x :: l) = x :: tested v l := by sorry
