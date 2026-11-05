-- Prove2me | Theorems.Thm_Eight_ViaGrouping_size_bound
-- name    : Eight.ViaGrouping.size_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:23:21.370408+00:00
-- url     : https://prove2.me/theorems/8b3ad4cc-1002-4b90-8cb0-dc8d874f651c
-- title:
--   Via Grouping: size bound
-- statement:
--   The sizes of the states: a polynomial in the size s of Φ. Here μ = m̄ ≤ m < s and P ≤ 2kμ + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Count.lean#L53-L75
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Count.lean#L53-L75

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_SatPsi
import Definitions.Def_Eight_SecProof_Network
import Definitions.Def_Eight_SecProof_Proof
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Count
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Paper

theorem Eight.ViaGrouping.size_bound {g k C₁ A s μ P : ℕ} (hμ : μ + 1 ≤ s) (hP : P ≤ 2 * (μ * k) + 1) (hA : (6 * k + 2 * g + 11) + C₁ * (2 * k + 3) ^ C₁ + C₁ + 1 ≤ A) :
    s + 2 * g + 6 * (μ * k) + 10 + C₁ * (s + P + 1) ^ C₁ ≤ A * s ^ A := by sorry
