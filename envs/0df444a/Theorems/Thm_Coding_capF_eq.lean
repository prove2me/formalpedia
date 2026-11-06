-- Prove2me | Theorems.Thm_Coding_capF_eq
-- name    : Coding.capF_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:06:36.382341+00:00
-- url     : https://prove2.me/theorems/e360f65d-dc7b-4bea-bae8-b1db03f28532
-- title:
--   Coding: cap F eq
-- statement:
--   «c_{a,b} is the number of tests with one occurrence in cluster a and the other in cluster b»
--   (Section 6): Lean's number c_{a,b} is the number of tests between the clusters a and b.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLinks.lean#L150-L158
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLinks.lean#L150-L158

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_OccLists
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Mathlib.Tactic.Ring
import Definitions.Def_Coding_OccLinks
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

theorem Coding.capF_eq (hg : 0 < g) (h3 : ∀ C ∈ Φ, C.length ≤ 3) (a b : ℕ) : capF g 3 Φ a b = (testsBetween g Φ a b).length := by sorry
