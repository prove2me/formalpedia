-- Prove2me | Theorems.Thm_Coding_map_links
-- name    : Coding.map_links
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:32:01.900988+00:00
-- url     : https://prove2.me/theorems/568381e0-6238-4578-8be2-a7dc9cf0445e
-- title:
--   Coding: map links
-- statement:
--   Whatever is read off the links of Lean's network, place by place, is read off the tests.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLinks.lean#L142-L146
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLinks.lean#L142-L146

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

theorem Coding.map_links (hg : 0 < g) (h3 : ∀ C ∈ Φ, C.length ≤ 3) {a b : ℕ} (hab : a ≤ b) {β : Type} (F : ℕ × ℕ → β) :
    (links g 3 Φ a b).map (fun p => F (a * (mu g Φ * 3) + p.1, b * (mu g Φ * 3) + p.2)) = (testsBetween g Φ a b).map fun p => F (place p.1, place p.2) := by sorry
