-- Prove2me | Theorems.Thm_Exits_met_cons_of_stop
-- name    : Exits.met_cons_of_stop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:51:21.827593+00:00
-- url     : https://prove2.me/theorems/72fd5381-3334-4843-869e-39fef0ee16d9
-- title:
--   Exits: met cons of stop
-- statement:
--   If the accumulator passes `stop` after the first round, the loop is left.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L151-L151
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L151-L151

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

theorem Exits.met_cons_of_stop {f : γ → τ → γ} {stop : γ → Bool} {c : γ} {x : τ} (h : stop (f c x) = true) (xs : List τ) : met f stop c (x :: xs) = [x] := by sorry
