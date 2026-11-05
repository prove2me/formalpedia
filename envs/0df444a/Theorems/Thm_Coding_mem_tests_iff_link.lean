-- Prove2me | Theorems.Thm_Coding_mem_tests_iff_link
-- name    : Coding.mem_tests_iff_link
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:05:55.39589+00:00
-- url     : https://prove2.me/theorems/8f6ad60b-9383-474e-bb64-cf1be4adc7c2
-- title:
--   Coding: mem tests iff link
-- statement:
--   A pair of places is a link exactly if the pair of their occurrences is a test.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccTests.lean#L61-L67
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccTests.lean#L61-L67

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

theorem Coding.mem_tests_iff_link (h3 : ∀ C ∈ Φ, C.length ≤ 3) (p q : Slot 1 Φ.length 3) : (occOfSlot p, occOfSlot q) ∈ tests Φ ↔ Link Φ p q := by sorry
