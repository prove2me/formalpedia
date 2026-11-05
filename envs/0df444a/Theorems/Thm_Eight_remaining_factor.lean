-- Prove2me | Theorems.Thm_Eight_remaining_factor
-- name    : Eight.remaining_factor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:31:14.176834+00:00
-- url     : https://prove2.me/theorems/b4975b58-0210-4a83-aa50-478509e5ab98
-- title:
--   Eight: remaining factor
-- statement:
--   The same with τ = 1, the cost of a query to the network of Φ in the model used here (a value of
--   W or f is computed in one step; that these steps take polynomial time is
--   `Groundwork.Prog.satP_keeps`):
--   C₁·2^{δ'g}·(6⌈m/g⌉ + 1)^{C₁} ≤ A·2^{δ'm/4} for every m.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Network.lean#L373-L382
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Network.lean#L373-L382

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

theorem Eight.remaining_factor (C₁ g : ℕ) {δ' : ℝ} (hδ' : 0 < δ') : ∃ A : ℕ, ∀ m : ℕ,
    (C₁ : ℝ) * (2 : ℝ) ^ (δ' * g) * ((6 * ((m + g - 1) / g) + 1 : ℕ) : ℝ) ^ C₁ ≤ A * (2 : ℝ) ^ (δ' * m / 4) := by sorry
