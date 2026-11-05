-- Prove2me | Theorems.Thm_Eight_card_testsOf_add
-- name    : Eight.card_testsOf_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:31:49.887847+00:00
-- url     : https://prove2.me/theorems/cda6dc9b-2604-476d-bae8-05158be95a68
-- title:
--   Eight: card tests Of add
-- statement:
--   «The total number of tests is the number of occurrences minus the number of variables that
--   occur», written without subtraction.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Network.lean#L214-L216
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Network.lean#L214-L216

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
variable {Φ : Formula} {g μ k : ℕ}

theorem Eight.card_testsOf_add (hk : ∀ C ∈ Φ, C.length ≤ k) (hm : Φ.length ≤ g * μ) : #(testsOf Φ g μ k) + #(occurring Φ) = #(occurrencesOf Φ g μ k) := by sorry
