-- Prove2me | Theorems.Thm_Eight_ViaGrouping_satF_eq
-- name    : Eight.ViaGrouping.satF_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:04:47.712118+00:00
-- url     : https://prove2.me/theorems/c5b61e70-6198-4558-9045-c15a50356f05
-- title:
--   Via Grouping: sat F eq
-- statement:
--   «f_{a,b}(z_a, θ) = [z_a|_b = θ]», θ ∈ {0,1}^{c_{a,b}}: the function f of the network `wordNet`
--   is the one that the paper prints.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/SatPsi.lean#L46-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/SatPsi.lean#L46-L55

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

theorem Eight.ViaGrouping.satF_eq (a b : ℕ) (z : List Bool) {θ : List Bool} (hθ : θ.length = capF g k Φ a b) : fF g k (Φ, ((a, b), (z, θ))) = if restr g k Φ a b z = θ then 1 else 0 := by sorry
