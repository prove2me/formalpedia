-- Prove2me | Theorems.Thm_Eight_card_testsOf_eq
-- name    : Eight.card_testsOf_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:35:54.530194+00:00
-- url     : https://prove2.me/theorems/14c7b659-9e80-41c3-a74a-bf86da261f4a
-- title:
--   Eight: card tests Of eq
-- statement:
--   There are as many tests as occurrences that are not the first of their variable.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Network.lean#L163-L176
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Network.lean#L163-L176

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
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Eight
open Finset Groundwork Groundwork.Prog Groundwork.SatNet Paper
variable {Φ : Formula} {g μ k : ℕ}

theorem Eight.card_testsOf_eq : #(testsOf Φ g μ k) = #{q ∈ occurrencesOf Φ g μ k | ∃ p, Link Φ p q} := by sorry
