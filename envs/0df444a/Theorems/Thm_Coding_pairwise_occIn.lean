-- Prove2me | Theorems.Thm_Coding_pairwise_occIn
-- name    : Coding.pairwise_occIn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:04:09.45721+00:00
-- url     : https://prove2.me/theorems/a3a7085e-5219-4e40-ac31-8386435bb8a9
-- title:
--   Coding: pairwise occ In
-- statement:
--   The reading order of the occurrences is the order of their places.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLists.lean#L140-L154
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLists.lean#L140-L154

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

theorem Coding.pairwise_occIn (h3 : ∀ C ∈ Φ, C.length ≤ 3) (e₀ r : ℕ) : (occIn Φ e₀ r).Pairwise fun o o' => place o < place o' := by sorry
