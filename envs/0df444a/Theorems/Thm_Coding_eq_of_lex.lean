-- Prove2me | Theorems.Thm_Coding_eq_of_lex
-- name    : Coding.eq_of_lex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:03:52.698201+00:00
-- url     : https://prove2.me/theorems/ca809dec-8d45-465d-811a-64fbeca42310
-- title:
--   Coding: eq of lex
-- statement:
--   Two lists of pairs of numbers that are increasing in the order of the dictionary and have the
--   same members are equal.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLists.lean#L55-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLists.lean#L55-L63

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_Defs
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Mathlib.Data.List.ProdSigma
import Definitions.Def_Coding_OccLists
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Coding
open Groundwork Groundwork.Prog Groundwork.Prog.Count

theorem Coding.eq_of_lex {l₁ l₂ : List (ℕ × ℕ)} (h₁ : l₁.Pairwise lexLt) (h₂ : l₂.Pairwise lexLt) (h : ∀ q, q ∈ l₁ ↔ q ∈ l₂) : l₁ = l₂ := by sorry
