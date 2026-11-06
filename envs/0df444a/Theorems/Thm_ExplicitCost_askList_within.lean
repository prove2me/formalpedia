-- Prove2me | Theorems.Thm_ExplicitCost_askList_within
-- name    : ExplicitCost.askList_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:05:33.650028+00:00
-- url     : https://prove2.me/theorems/b405f96e-1700-49b1-910c-ba2998db675a
-- title:
--   Explicit Cost: ask List within
-- statement:
--   One query, read as a list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverStages.lean#L38-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverStages.lean#L38-L39

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverDefs
import Definitions.Def_CountedRecursion_Within
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverStages
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork QueryMachines Printed
variable {Q α : Type}

theorem ExplicitCost.askList_within [HasSize α] {h : α → Q} {O : Q → Option Ans} {w : Q → ℕ} {a : α} {v : Ans} (hv : O (h a) = some v) : (askList h).Within O w a (w (h a)) (max (size a) (size v) + 1) (asList v) := by sorry
