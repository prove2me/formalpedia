-- Prove2me | Theorems.Thm_Exits_met_first
-- name    : Exits.met_first
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:45:19.722197+00:00
-- url     : https://prove2.me/theorems/53e677f9-b096-4463-ae3c-edc1400b4ad4
-- title:
--   Exits: met first
-- statement:
--   The loop of «try all … until one is good»: the accumulator holds the first good number, if one
--   has been seen, and the loop is left as soon as it holds one. The points met are those tested.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L177-L191
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L177-L191

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

theorem Exits.met_first (p : β → Bool) (v : ℕ → β) (a : α) (l : List ℕ) :
    met (fun c (x : α × ℕ) => rangeG (firstG p) c x (v x.2)) Option.isSome none (l.map fun y => (a, y)) = (tested (fun y => p (v y)) l).map fun y => (a, y) := by sorry
