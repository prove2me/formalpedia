-- Prove2me | Theorems.Thm_Coding_mem_testsBetween
-- name    : Coding.mem_testsBetween
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T01:05:32.212251+00:00
-- url     : https://prove2.me/theorems/9c0cd1f1-b988-4adb-9028-2ffa6238a260
-- title:
--   Coding: mem tests Between
-- statement:
--   For a ≤ b the earlier occurrence of a test between the clusters a and b lies in cluster a.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLinks.lean#L67-L86
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLinks.lean#L67-L86

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

theorem Coding.mem_testsBetween (h3 : ∀ C ∈ Φ, C.length ≤ 3) {a b : ℕ} (hab : a ≤ b) {p : (ℕ × ℕ) × (ℕ × ℕ)} :
    p ∈ testsBetween g Φ a b ↔ p ∈ tests Φ ∧ clusterOf g Φ p.1 = a ∧ clusterOf g Φ p.2 = b := by sorry
