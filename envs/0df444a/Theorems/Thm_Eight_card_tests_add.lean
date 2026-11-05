-- Prove2me | Theorems.Thm_Eight_card_tests_add
-- name    : Eight.card_tests_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:38:17.574006+00:00
-- url     : https://prove2.me/theorems/43ef9a19-c269-4839-96b6-e4872a03806c
-- title:
--   Eight: card tests add
-- statement:
--   **Section 6.** «The total number of tests is the number of occurrences minus the number of
--   variables that occur». Same as in the paper; written without subtraction.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Network.lean#L299-L300
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Network.lean#L299-L300

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecProof_NetworkDefs
import Definitions.Def_SingleBitPieces_SecProof_Cost
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Mathlib.Tactic
import Definitions.Def_Eight_SecProof_Network
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight
open Finset Groundwork Groundwork.Prog Groundwork.SatNet Paper

theorem Eight.card_tests_add {g : ℕ} (hg : 0 < g) {Φ : Formula} (h3 : ∀ C ∈ Φ, C.length ≤ 3) : #(tests g Φ) + #(occurring Φ) = #(occurrences g Φ) := by sorry
