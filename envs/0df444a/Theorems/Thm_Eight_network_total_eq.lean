-- Prove2me | Theorems.Thm_Eight_network_total_eq
-- name    : Eight.network_total_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:38:28.274822+00:00
-- url     : https://prove2.me/theorems/66fb9a51-6b50-4fba-a494-debdb59a3e3c
-- title:
--   Eight: network total eq
-- statement:
--   **Section 6, «Cost».** «U counts each test between two clusters twice». Same as in the paper.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Network.lean#L316-L318
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Network.lean#L316-L318

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

theorem Eight.network_total_eq {g : ℕ} (hg : 0 < g) (Φ : Formula) : (networkOf g Φ).U = 2 * #{t ∈ tests g Φ | t.1.1 ≠ t.2.1} := by sorry
