-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Correct_onFormula
-- name    : Eight.ViaGrouping.Correct.onFormula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:17:36.463851+00:00
-- url     : https://prove2.me/theorems/4f1bd910-dcf1-41b0-a064-05d3f5ffe73a
-- title:
--   Correct: on Formula
-- statement:
--   **Lemma 1, applied to the network of Φ.** If NA obeys the bound of Lemma 1 with the exponent ε·U +
--   b·gP/K, then on the procedures of the network of Φ it returns the value Z of that network within
--   C₁·2^{εU + b·gP/K}·(P + 1)^{C₁} steps: B = 1 and τ = 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Count.lean#L36-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Count.lean#L36-L46

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

theorem Eight.ViaGrouping.Correct.onFormula {NA : NetAlg} {g K : ℕ} {ε b : ℝ} (hg : 0 < g) (k : ℕ) (h : Correct NA g K ε b) :
    ∃ C₁ : ℕ, ∀ Φ : Fml, ∃ T : ℕ,
      (NA.app (satProcs g k)).Runs Φ T (size Φ + 2 * g + 6 * (mu g Φ * k) + 10 + C₁ * (size Φ + satPf g k Φ + 1) ^ C₁) (wordNet g k Φ).value ∧
      (T : ℝ) ≤ C₁ * (2 : ℝ) ^ (ε * ((wordNet g k Φ).U : ℝ) + b * ((g : ℝ) * (satPf g k Φ : ℝ)) / K) * ((satPf g k Φ : ℝ) + 1) ^ C₁ := by sorry
