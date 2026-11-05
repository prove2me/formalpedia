-- Prove2me | Theorems.Thm_Exits_tested_nil
-- name    : Exits.tested_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:48:42.60275+00:00
-- url     : https://prove2.me/theorems/d98d8732-5933-44b4-b86e-f3e5d951a38d
-- title:
--   Exits: tested nil
-- statement:
--   Nothing is tested in the empty list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L32-L32
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L32-L32

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

theorem Exits.tested_nil (v : ν → Bool) : tested v [] = [] := by sorry
