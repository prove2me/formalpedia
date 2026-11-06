-- Prove2me | Theorems.Thm_Eight_ViaGrouping_satPsiM_isPolyT
-- name    : Eight.ViaGrouping.satPsiM_isPolyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:05:00.99247+00:00
-- url     : https://prove2.me/theorems/26da4e6c-e34b-4428-a083-c2df565417c4
-- title:
--   Via Grouping: sat Psi M is Poly T
-- statement:
--   The procedure for Ψ has polynomial-time steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/SatPsi.lean#L85-L85
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/SatPsi.lean#L85-L85

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

theorem Eight.ViaGrouping.satPsiM_isPolyT (g k : ℕ) : Nonempty (IsPolyT (satPsiM g k)) := by sorry
