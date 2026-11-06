-- Prove2me | Theorems.Thm_Coding_pairwise_tests
-- name    : Coding.pairwise_tests
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:04:05.173435+00:00
-- url     : https://prove2.me/theorems/ccefb56d-51a3-4ad6-80a8-6bdebbad72c4
-- title:
--   Coding: pairwise tests
-- statement:
--   The tests, read as pairs of places, are listed in the order of the dictionary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLinks.lean#L89-L94
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLinks.lean#L89-L94

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

theorem Coding.pairwise_tests (h3 : ∀ C ∈ Φ, C.length ≤ 3) : ((tests Φ).map fun p => (place p.1, place p.2)).Pairwise lexLt := by sorry
