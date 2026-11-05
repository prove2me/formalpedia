-- Prove2me | Theorems.Thm_Eight_ViaGrouping_count_cost_of
-- name    : Eight.ViaGrouping.count_cost_of
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:19:15.29493+00:00
-- url     : https://prove2.me/theorems/03f1b723-748f-4e44-94fb-c3087261f1f4
-- title:
--   Via Grouping: count cost of
-- statement:
--   **Section 6, «Cost», for a named algorithm.** «So … Z is computed in time O(2^{δ'm})», and «Z is
--   the number of assignments of the variables occurring in Φ that satisfy Φ». If `NA` evaluates the
--   networks on [g], given as Definition 2 prints them, within the bound of
--   Lemma 1 with e = δ'/12 and K ≥ 72/δ', the constants of the paper, then `NA` on the network of Φ
--   (procedure COUNT of Algorithm 1) returns that number within A·2^{δ'm} steps, on states of polynomial
--   size. The proof goes through the sentences of the paper in their order:
--   Definition 2 holds, with P = 6m̄ and B = 1 (`satNet_isNetworkP`, inside `Correct.onFormula`); what Z
--   is (`network_value_eq`); U < 6m (`network_total_lt`) and gP ≤ 6(m + g); the exponent
--   (`network_exponent_lt'`); the remaining factor (`remaining_factor`).
--   Different from the paper: the case m = 0, which the paper sets apart, is run through the same
--   machine (then U = 0, P = 1, P + B = 2 ≤ 2(6m̄ + 1), which costs the constant factor 2^{C₁}, and the
--   exponent is at most δ'g); only steps are counted here (they take polynomial time when those of `NA`
--   do: `satProcs_keepsP`), so τ = 1 and there
--   is no «preparation in time polynomial in n».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Count.lean#L109-L166
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Count.lean#L109-L166

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Paper

theorem Eight.ViaGrouping.count_cost_of {g K : ℕ} {δ' : ℝ} {NA : NetAlg} (hδ' : 0 < δ') (h1 : δ' ≤ 1) (hg : 0 < g) (hK : 72 / δ' ≤ K)
    (h : Correct NA g K (δ' / 12) (δ' / 12 + 2)) :
    ∃ A : ℕ, ∀ Φ : Formula, (∀ C ∈ Φ, C.length ≤ 3) →
      ∃ T : ℕ, (NA.app (satProcs g 3)).Runs Φ T (A * size Φ ^ A) (numSat Φ) ∧ (T : ℝ) ≤ A * (2 : ℝ) ^ (δ' * Φ.length) := by sorry
