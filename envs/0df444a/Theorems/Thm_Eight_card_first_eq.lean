-- Prove2me | Theorems.Thm_Eight_card_first_eq
-- name    : Eight.card_first_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:35:43.257885+00:00
-- url     : https://prove2.me/theorems/51541a1f-a381-445c-b24a-b1087d5b4298
-- title:
--   Eight: card first eq
-- statement:
--   There are as many first occurrences as variables that occur.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Network.lean#L179-L210
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Network.lean#L179-L210

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

theorem Eight.card_first_eq (hk : ∀ C ∈ Φ, C.length ≤ k) (hm : Φ.length ≤ g * μ) : #{q ∈ occurrencesOf Φ g μ k | ¬ ∃ p, Link Φ p q} = #(occurring Φ) := by sorry
