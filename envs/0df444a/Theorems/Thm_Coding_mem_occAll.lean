-- Prove2me | Theorems.Thm_Coding_mem_occAll
-- name    : Coding.mem_occAll
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:35:13.883835+00:00
-- url     : https://prove2.me/theorems/ec3dd06d-95f9-4386-ba88-d70713e5ce70
-- title:
--   Coding: mem occ All
-- statement:
--   (e, j) is an occurrence in Φ if j is a position of clause e.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLists.lean#L127-L132
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLists.lean#L127-L132

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

theorem Coding.mem_occAll {o : ℕ × ℕ} : o ∈ occAll Φ ↔ o.2 < (Φ.getD o.1 []).length := by sorry
