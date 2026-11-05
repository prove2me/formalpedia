-- Prove2me | Theorems.Thm_Coding_fst_lt_of_mem_occAll
-- name    : Coding.fst_lt_of_mem_occAll
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:21:47.988782+00:00
-- url     : https://prove2.me/theorems/5136302b-44a4-4880-a10b-fb80c60823ef
-- title:
--   Coding: fst lt of mem occ All
-- statement:
--   The clause of an occurrence is one of the clauses of Φ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLists.lean#L135-L137
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLists.lean#L135-L137

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

theorem Coding.fst_lt_of_mem_occAll {o : ℕ × ℕ} (h : o ∈ occAll Φ) : o.1 < Φ.length := by sorry
