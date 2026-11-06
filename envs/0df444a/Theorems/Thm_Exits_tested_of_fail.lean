-- Prove2me | Theorems.Thm_Exits_tested_of_fail
-- name    : Exits.tested_of_fail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:44:20.933591+00:00
-- url     : https://prove2.me/theorems/62e6fff4-ab66-4746-801e-f3afdc6ce39b
-- title:
--   Exits: tested of fail
-- statement:
--   If no entry passes, all are tested.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L47-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L47-L52

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

theorem Exits.tested_of_fail {v : ν → Bool} {l : List ν} (h : l.any v = false) : tested v l = l := by sorry
