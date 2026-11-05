-- Prove2me | Theorems.Thm_Eight_ViaGrouping_satNet_isNetworkP
-- name    : Eight.ViaGrouping.satNet_isNetworkP
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T00:08:15.699078+00:00
-- url     : https://prove2.me/theorems/9c2af36a-b786-4a86-b205-350cb50c05b1
-- title:
--   Via Grouping: sat Net is Network P
-- statement:
--   **Section 6.** «The network of Φ is the following network on [g] with P = 6m̄ and B = 1. …
--   Definition 2 holds: Σ_{b ≠ a} c_{a,b} ≤ 2·3m̄ = P, all values are 0 or 1, and τ is polynomial in m».
--   The network of Φ, with the procedure `satPsiM` for Ψ, is a network in the sense
--   of Definition 2 (without the part of condition (iii) that gives B to the algorithm as input), with
--   parameters P = max{1, 2k·m̄}, B = 1, τ = 1; it has the value and the total of the network `wordNet`.
--   Different from the paper: k literals per clause in place of 3; P ≥ 1 also if Φ has no clause; τ = 1,
--   since a value is computed in
--   one step, which takes polynomial time (`satProcs_keepsP`); every string of k·m̄ bits is a setting (a
--   clause has k places, and W is 0 unless the bits at places without a literal are 0).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/SatPsi.lean#L120-L124
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/SatPsi.lean#L120-L124

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

theorem Eight.ViaGrouping.satNet_isNetworkP (hg : 0 < g) (k : ℕ) (Φ : Fml) :
    IsNetworkP (satProcs g k) Φ (satNet g k Φ) (satPf g k Φ) 1 1 (size Φ + 2 * g + 6 * (mu g Φ * k) + 8 + 2) ∧ (satNet g k Φ).value = (wordNet g k Φ).value ∧ (satNet g k Φ).U = (wordNet g k Φ).U := by sorry
