-- Prove2me | Theorems.Thm_Coding_clusterOf_eq_iff
-- name    : Coding.clusterOf_eq_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:04:24.833205+00:00
-- url     : https://prove2.me/theorems/ff59058d-730b-4383-a87e-6d396f7872b4
-- title:
--   Coding: cluster Of eq iff
-- statement:
--   The cluster of an occurrence is the block of 3·m̄ places in which its place lies.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLinks.lean#L43-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLinks.lean#L43-L50

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

theorem Coding.clusterOf_eq_iff (hg : 0 < g) (h3 : ∀ C ∈ Φ, C.length ≤ 3) {o : ℕ × ℕ} (ho : o ∈ occAll Φ) (a : ℕ) :
    clusterOf g Φ o = a ↔ a * (mu g Φ * 3) ≤ place o ∧ place o < a * (mu g Φ * 3) + mu g Φ * 3 := by sorry
