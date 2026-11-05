-- Prove2me | Theorems.Thm_Coding_mem_occurrencesOf_iff
-- name    : Coding.mem_occurrencesOf_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T02:32:46.226196+00:00
-- url     : https://prove2.me/theorems/04a38b0b-90b6-4f9a-98cc-6fc181eb4781
-- title:
--   Coding: mem occurrences Of iff
-- statement:
--   A place holds a literal exactly if its pair is an occurrence.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccTests.lean#L49-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccTests.lean#L49-L58

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

theorem Coding.mem_occurrencesOf_iff (p : Slot 1 Φ.length 3) : p ∈ occurrencesOf Φ 1 Φ.length 3 ↔ occOfSlot p ∈ occAll Φ := by sorry
