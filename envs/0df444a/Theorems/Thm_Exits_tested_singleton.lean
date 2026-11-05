-- Prove2me | Theorems.Thm_Exits_tested_singleton
-- name    : Exits.tested_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:53:38.521077+00:00
-- url     : https://prove2.me/theorems/c9885a6c-164a-42bd-8e39-2879d30366d9
-- title:
--   Exits: tested singleton
-- statement:
--   A single entry is tested, whatever the outcome.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L41-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L41-L41

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

theorem Exits.tested_singleton (v : ν → Bool) (x : ν) : tested v [x] = [x] := by sorry
