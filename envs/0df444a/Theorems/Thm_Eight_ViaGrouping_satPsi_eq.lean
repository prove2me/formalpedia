-- Prove2me | Theorems.Thm_Eight_ViaGrouping_satPsi_eq
-- name    : Eight.ViaGrouping.satPsi_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:31:14.161419+00:00
-- url     : https://prove2.me/theorems/4ea3a5d4-90ea-429c-86c6-dae15903bf25
-- title:
--   Via Grouping: sat Psi eq
-- statement:
--   **Ψ of the network of Φ.** «Put Ψ_{a,b}(z_a, z_b) = [z_a|_b = z_b|_a]»: the function `satPsi` is
--   the Ψ_{a,b} of the network `wordNet` (there: the sum over θ of f_{a,b}·f_{b,a}).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/SatPsi.lean#L59-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/SatPsi.lean#L59-L72

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

theorem Eight.ViaGrouping.satPsi_eq {a b : Fin g} (hab : a ≠ b) (z z' : List Bool) : satPsi g k Φ ((a.val, b.val), (z, z')) = (wordNet g k Φ).Ψ a b z z' := by sorry
