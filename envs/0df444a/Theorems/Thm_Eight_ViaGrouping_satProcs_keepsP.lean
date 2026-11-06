-- Prove2me | Theorems.Thm_Eight_ViaGrouping_satProcs_keepsP
-- name    : Eight.ViaGrouping.satProcs_keepsP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:07:57.03439+00:00
-- url     : https://prove2.me/theorems/762c846a-3f25-4602-907d-788fa90c2711
-- title:
--   Via Grouping: sat Procs keeps P
-- statement:
--   The procedures of the network of a formula have polynomial-time steps, the lengths P_a, c_{a,b}
--   and the number P are given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/SatPsi.lean#L107-L107
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/SatPsi.lean#L107-L107

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
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.SatNet Eight.SecNetworks
variable {g k : ℕ} {Φ : Fml}

theorem Eight.ViaGrouping.satProcs_keepsP (g k : ℕ) : KeepsP (satProcs g k) := by sorry
