-- Prove2me | Theorems.Thm_Coding_mem_occIn
-- name    : Coding.mem_occIn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:55:04.481506+00:00
-- url     : https://prove2.me/theorems/c4167f9c-67ed-4d70-808f-56fe03224724
-- title:
--   Coding: mem occ In
-- statement:
--   (e, j) is an occurrence in the clauses number e₀, …, e₀ + r − 1 if e is one of these numbers and
--   j is a position of clause e.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLists.lean#L117-L124
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLists.lean#L117-L124

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_Defs
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Mathlib.Data.List.ProdSigma
import Definitions.Def_Coding_OccLists
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Coding
open Groundwork Groundwork.Prog Groundwork.Prog.Count
variable {g : ℕ} {Φ : Fml}

theorem Coding.mem_occIn {e₀ r : ℕ} {o : ℕ × ℕ} : o ∈ occIn Φ e₀ r ↔ e₀ ≤ o.1 ∧ o.1 < e₀ + r ∧ o.2 < (Φ.getD o.1 []).length := by sorry
