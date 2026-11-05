-- Prove2me | Theorems.Thm_Eight_network_total_le_twice
-- name    : Eight.network_total_le_twice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:40:38.628271+00:00
-- url     : https://prove2.me/theorems/d4958c09-f852-4949-8f08-9fa8566b4da0
-- title:
--   Eight: network total le twice
-- statement:
--   **Section 6, «Cost».** «… so U ≤ 2(3m − 1)», for m ≥ 1. Same as in the paper.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Network.lean#L321-L323
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Network.lean#L321-L323

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

theorem Eight.network_total_le_twice {g : ℕ} (hg : 0 < g) {Φ : Formula} (h3 : ∀ C ∈ Φ, C.length ≤ 3) (hm : 1 ≤ Φ.length) : (networkOf g Φ).U ≤ 2 * (3 * Φ.length - 1) := by sorry
