-- Prove2me | Theorems.Thm_Exits_met_or
-- name    : Exits.met_or
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:44:57.665055+00:00
-- url     : https://prove2.me/theorems/7557a7d6-f1a6-4849-87ea-bda44f0c60e4
-- title:
--   Exits: met or
-- statement:
--   The loop of «if … then return»: the accumulator says whether some point has passed so far, and
--   the loop is left as soon as it says yes. The points met are those tested.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L158-L167
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L158-L167

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

theorem Exits.met_or (w : τ → Bool) (xs : List τ) : met (fun c x => c || w x) id false xs = tested w xs := by sorry
