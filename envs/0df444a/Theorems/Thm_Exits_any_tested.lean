-- Prove2me | Theorems.Thm_Exits_any_tested
-- name    : Exits.any_tested
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:45:02.651762+00:00
-- url     : https://prove2.me/theorems/5f6299ea-89b4-449f-afc1-ca99b6e2b52e
-- title:
--   Exits: any tested
-- statement:
--   Some tested entry passes if and only if some entry passes.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L75-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L75-L81

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

theorem Exits.any_tested (v : ν → Bool) (l : List ν) : (tested v l).any v = l.any v := by sorry
