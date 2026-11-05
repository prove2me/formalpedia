-- Prove2me | Theorems.Thm_Eight_network_value_eq
-- name    : Eight.network_value_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:31:06.117628+00:00
-- url     : https://prove2.me/theorems/69eec961-7e15-40f6-a508-f196e753083b
-- title:
--   Eight: network value eq
-- statement:
--   **Section 6.** «Hence Z is the number of assignments of the variables occurring in Φ that
--   satisfy Φ.» Z is the value of the network of Φ on g ≥ 1 clusters; Φ has at most 3 literals per
--   clause. Same as in the paper.
--   (Empty clauses are allowed here; then both sides are 0.) The proof goes through the sentence before
--   it, «a term is 1 exactly if all occurrences of each variable carry the same bit and every clause has
--   a true occurrence»
--   (`Groundwork.SatNet.value_eq_card_good`), and a bijection between such terms and the satisfying
--   assignments.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Network.lean#L62-L93
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Network.lean#L62-L93

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

theorem Eight.network_value_eq {g : ℕ} (hg : 0 < g) (Φ : Formula) (h3 : ∀ C ∈ Φ, C.length ≤ 3) : (networkOf g Φ).value = numSat Φ := by sorry
