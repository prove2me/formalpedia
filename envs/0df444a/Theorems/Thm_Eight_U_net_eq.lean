-- Prove2me | Theorems.Thm_Eight_U_net_eq
-- name    : Eight.U_net_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:37:37.907002+00:00
-- url     : https://prove2.me/theorems/bb8af4a5-6dff-48d3-8a70-608016fa444f
-- title:
--   Eight: U net eq
-- statement:
--   «U counts each test between two clusters twice», for the network on functions
--   (`Groundwork.SatNet.net`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Network.lean#L276-L284
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Network.lean#L276-L284

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

theorem Eight.U_net_eq : (net Φ g μ k).U = 2 * #{t ∈ testsOf Φ g μ k | t.1.1 ≠ t.2.1} := by sorry
