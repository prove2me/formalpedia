-- Prove2me | Theorems.Thm_Exits_met_cons_of_go
-- name    : Exits.met_cons_of_go
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:51:20.776839+00:00
-- url     : https://prove2.me/theorems/6e164f73-29e9-40eb-b62a-03cf99be430f
-- title:
--   Exits: met cons of go
-- statement:
--   If it does not, the loop goes on with the new accumulator.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L154-L154
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L154-L154

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

theorem Exits.met_cons_of_go {f : γ → τ → γ} {stop : γ → Bool} {c : γ} {x : τ} (h : stop (f c x) = false) (xs : List τ) : met f stop c (x :: xs) = x :: met f stop (f c x) xs := by sorry
