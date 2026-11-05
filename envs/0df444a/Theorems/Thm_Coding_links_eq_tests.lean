-- Prove2me | Theorems.Thm_Coding_links_eq_tests
-- name    : Coding.links_eq_tests
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T02:30:29.039345+00:00
-- url     : https://prove2.me/theorems/57ae233e-df91-4e86-b1aa-dc76624d55bd
-- title:
--   Coding: links eq tests
-- statement:
--   The tests between two clusters are Lean's links, in the same order («Choose an order of these
--   tests», Section 6).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLinks.lean#L98-L139
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLinks.lean#L98-L139

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
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open Coding
open Groundwork Groundwork.Prog Groundwork.Prog.Count
variable {g : ℕ} {Φ : Fml}

theorem Coding.links_eq_tests (hg : 0 < g) (h3 : ∀ C ∈ Φ, C.length ≤ 3) {a b : ℕ} (hab : a ≤ b) :
    (links g 3 Φ a b).map (fun p => (a * (mu g Φ * 3) + p.1, b * (mu g Φ * 3) + p.2)) = (testsBetween g Φ a b).map fun p => (place p.1, place p.2) := by sorry
