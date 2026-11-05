-- Prove2me | Theorems.Thm_Exits_foldl_or
-- name    : Exits.foldl_or
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T17:45:25.255804+00:00
-- url     : https://prove2.me/theorems/1fef35d0-0127-458e-9216-207757116289
-- title:
--   Exits: foldl or
-- statement:
--   The result of that loop.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L170-L173
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L170-L173

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

theorem Exits.foldl_or (w : τ → Bool) (xs : List τ) (c : Bool) : xs.foldl (fun c x => c || w x) c = (c || xs.any w) := by sorry
