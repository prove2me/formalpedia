-- Prove2me | Theorems.Thm_Eight_sum_card_tests_eq
-- name    : Eight.sum_card_tests_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:37:14.497625+00:00
-- url     : https://prove2.me/theorems/638df7c5-cb44-4ba3-abb9-c30c629879df
-- title:
--   Eight: sum card tests eq
-- statement:
--   The tests between two different clusters, sorted by the cluster of the first and the cluster of
--   the second occurrence.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Network.lean#L256-L272
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Network.lean#L256-L272

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

theorem Eight.sum_card_tests_eq : ∑ a : Fin g, ∑ b ∈ univ.erase a, #{t ∈ testsOf Φ g μ k | t.1.1 = a ∧ t.2.1 = b} = #{t ∈ testsOf Φ g μ k | t.1.1 ≠ t.2.1} := by sorry
