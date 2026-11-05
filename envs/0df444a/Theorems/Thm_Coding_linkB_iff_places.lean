-- Prove2me | Theorems.Thm_Coding_linkB_iff_places
-- name    : Coding.linkB_iff_places
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:05:47.817951+00:00
-- url     : https://prove2.me/theorems/174a1785-1964-4e85-8135-6f51f98eb4b9
-- title:
--   Coding: link B iff places
-- statement:
--   Lean's link between two places, in words.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLists.lean#L201-L203
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLists.lean#L201-L203

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

theorem Coding.linkB_iff_places (i i' : ℕ) : linkB 3 Φ i i' = true ↔ i < i' ∧ (varAt 3 Φ i).isSome = true ∧ varAt 3 Φ i = varAt 3 Φ i' ∧
    ∀ t < Φ.length * 3, ¬ (i < t ∧ t < i' ∧ varAt 3 Φ t = varAt 3 Φ i) := by sorry
