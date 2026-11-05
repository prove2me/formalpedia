-- Prove2me | Theorems.Thm_Coding_toFinset_occAll
-- name    : Coding.toFinset_occAll
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:06:24.475906+00:00
-- url     : https://prove2.me/theorems/2e5d600d-f3a2-4dd1-bf14-b8e2680ba2bf
-- title:
--   Coding: to Finset occ All
-- statement:
--   The occurrences are the pairs of the slots that hold a literal.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccTests.lean#L87-L95
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccTests.lean#L87-L95

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_OccMore
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_Eight_SecProof_Network
import Definitions.Def_Coding_OccTests
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.SatNet Eight
variable {Φ : Fml}

theorem Coding.toFinset_occAll (h3 : ∀ C ∈ Φ, C.length ≤ 3) : (occAll Φ).toFinset = (occurrencesOf Φ 1 Φ.length 3).image occOfSlot := by sorry
