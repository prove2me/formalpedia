-- Prove2me | Theorems.Thm_Exits_foldl_first_tested
-- name    : Exits.foldl_first_tested
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T17:45:34.224551+00:00
-- url     : https://prove2.me/theorems/50722519-34fc-4c48-b725-048b406bcb21
-- title:
--   Exits: foldl first tested
-- statement:
--   The result of that loop: the first good number of the whole list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L194-L203
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L194-L203

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

theorem Exits.foldl_first_tested (p : β → Bool) (v : ℕ → β) (l : List ℕ) :
    (tested (fun y => p (v y)) l).foldl (fun c y => firstG p c y (v y)) none = l.find? fun y => p (v y) := by sorry
