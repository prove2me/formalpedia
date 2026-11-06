-- Prove2me | Theorems.Thm_ExplicitCost_readAs_reaches
-- name    : ExplicitCost.readAs_reaches
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:40:32.0014+00:00
-- url     : https://prove2.me/theorems/653fcee4-e37f-4f84-ae2d-ecf5f87c1400
-- title:
--   Explicit Cost: read As reaches
-- statement:
--   `readAs r M` runs as M does (from a state).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Answers.lean#L30-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Answers.lean#L30-L40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_AnswersDefs
import Definitions.Def_QueryMachines_Runs
import Definitions.Def_QueryMachines_Poly
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Answers
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines Printed
variable {Q A A' α β : Type}

theorem ExplicitCost.readAs_reaches {r : A' → A} {M : QueryMachine Q A α β} {O : Q → Option A} {O' : Q → Option A'} (h : ∀ x, (O' x).map r = O x) {S own : ℕ} {L : List Q} {b : β} {s : M.σ}
    (hr : M.Reaches O S b s own L) : (readAs r M).Reaches O' S b s own L := by sorry
