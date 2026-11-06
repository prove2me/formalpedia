-- Prove2me | Theorems.Thm_Coding_mem_occOf_iff
-- name    : Coding.mem_occOf_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:30:07.716186+00:00
-- url     : https://prove2.me/theorems/dad56fba-8e2b-40f5-bc65-534ad53357e9
-- title:
--   Coding: mem occ Of iff
-- statement:
--   The occurrences in cluster a are the occurrences whose cluster is a.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLinks.lean#L53-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLinks.lean#L53-L60

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_OccLists
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Mathlib.Tactic.Ring
import Definitions.Def_Coding_OccLinks
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Coding
open Groundwork Groundwork.Prog Groundwork.Prog.Count
variable {g : ℕ} {Φ : Fml}

theorem Coding.mem_occOf_iff (hg : 0 < g) {o : ℕ × ℕ} {a : ℕ} : o ∈ occOf g Φ a ↔ o ∈ occAll Φ ∧ clusterOf g Φ o = a := by sorry
