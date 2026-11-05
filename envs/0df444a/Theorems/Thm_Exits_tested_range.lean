-- Prove2me | Theorems.Thm_Exits_tested_range
-- name    : Exits.tested_range
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T17:44:54.257943+00:00
-- url     : https://prove2.me/theorems/0d2e9543-83af-4447-bf9e-548dfbc4c9a9
-- title:
--   Exits: tested range
-- statement:
--   In the range 0, …, n − 1 the numbers below `reach` are tested: «try all … until one is good».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L91-L107
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L91-L107

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

theorem Exits.tested_range (q : ℕ → Bool) (n : ℕ) : tested q (List.range n) = List.range (reach q n) := by sorry
