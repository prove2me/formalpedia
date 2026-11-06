-- Prove2me | Theorems.Thm_Eight_ViaGrouping_satPsiM_runs
-- name    : Eight.ViaGrouping.satPsiM_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:05:06.513421+00:00
-- url     : https://prove2.me/theorems/542b9d4f-9e1d-4305-b4ba-6745960f0435
-- title:
--   Via Grouping: sat Psi M runs
-- statement:
--   The procedure for Ψ answers a query on two settings in one step, on states of the size within
--   which the procedures for W and f answer.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/SatPsi.lean#L89-L96
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/SatPsi.lean#L89-L96

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_SatPsiDefs
import Definitions.Def_Eight_ViaGrouping_Bridge
import Definitions.Def_ToTuring_Poly_Count
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_SatPsi
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.SatNet Eight.SecNetworks
variable {g k : ℕ} {Φ : Fml}

theorem Eight.ViaGrouping.satPsiM_runs (a b : Fin g) {z z' : List Bool} (hz : z.length = mu g Φ * k) (hz' : z'.length = mu g Φ * k) :
    (satPsiM g k).Runs (Φ, ((a.val, b.val), (z, z'))) 1 (size Φ + 2 * g + 6 * (mu g Φ * k) + 8) (satPsi g k Φ ((a.val, b.val), (z, z'))) := by sorry
