-- Prove2me | Theorems.Thm_Eight_remaining_factor_query
-- name    : Eight.remaining_factor_query
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:38:38.622734+00:00
-- url     : https://prove2.me/theorems/97954d55-4933-46fe-b2f4-b04adbf17898
-- title:
--   Eight: remaining factor query
-- statement:
--   **Section 6, «Cost».** «The remaining factor C₁2^{δ'g}(P + B)^{C₁}τ is polynomial in m, hence
--   O(2^{δ'm/4})», with P = 6m̄, m̄ = ⌈m/g⌉ (written (m + g − 1)/g), B = 1 and a cost τ ≤ c(m + 1)^c of
--   a query: for all C₁, c, g and δ' > 0 there is a constant A with C₁·2^{δ'g}·(6m̄ + 1)^{C₁}·c(m + 1)^c
--   ≤ A·2^{δ'm/4} for every m. Same as in the paper, with «polynomial in m» for τ made explicit.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Network.lean#L341-L367
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Network.lean#L341-L367

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

theorem Eight.remaining_factor_query (C₁ c g : ℕ) {δ' : ℝ} (hδ' : 0 < δ') : ∃ A : ℕ, ∀ m : ℕ,
    (C₁ : ℝ) * (2 : ℝ) ^ (δ' * g) * ((6 * ((m + g - 1) / g) + 1 : ℕ) : ℝ) ^ C₁ * (c * ((m : ℝ) + 1) ^ c) ≤ A * (2 : ℝ) ^ (δ' * m / 4) := by sorry
