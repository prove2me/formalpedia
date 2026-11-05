-- Prove2me | Theorems.Thm_Coding_mem_occAll_of_varAt
-- name    : Coding.mem_occAll_of_varAt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T02:28:41.447371+00:00
-- url     : https://prove2.me/theorems/276440be-e96e-4b75-add9-8407356f1e8c
-- title:
--   Coding: mem occ All of var At
-- statement:
--   A place with a variable is the place of an occurrence.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLists.lean#L184-L188
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLists.lean#L184-L188

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
variable {g : ℕ} {Φ : Fml}

theorem Coding.mem_occAll_of_varAt {i v : ℕ} (h : varAt 3 Φ i = some v) : (i / 3, i % 3) ∈ occAll Φ := by sorry
