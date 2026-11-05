-- Prove2me | Theorems.Thm_Exits_reach_le
-- name    : Exits.reach_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:53:44.170064+00:00
-- url     : https://prove2.me/theorems/8bcb7500-1c33-4ed0-8baa-0bec446ee245
-- title:
--   Exits: reach le
-- statement:
--   The search does not go beyond the range.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L84-L88
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L84-L88

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

theorem Exits.reach_le (q : ℕ → Bool) (n : ℕ) : reach q n ≤ n := by sorry
