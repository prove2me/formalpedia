-- Prove2me | Theorems.Thm_Eight_ViaGrouping_ALGO_runs_of
-- name    : Eight.ViaGrouping.ALGO_runs_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:40:15.797941+00:00
-- url     : https://prove2.me/theorems/5e9d87bc-7965-41da-960c-a3a645fb9962
-- title:
--   Via Grouping: ALGO runs of
-- statement:
--   **The algorithm inside the circuit lower bound for E^NP (Section 7), with the procedure named.**
--   For every δ > 0 there are a level ℓ and a threshold parameter τ such that `En 3 ℓ τ` has
--   polynomial-time steps and the machine `CircuitLowerBound.Alg.algo (En 3 ℓ τ) F fb` ends on every
--   input x with the bit
--   «the formula made from x is unsatisfiable», within c·2^{δN} steps, N the number of variables of that
--   formula. F and fb stand for the functions that make the formula; the statement holds for every F
--   with `Alg.FormOK` and every fb. Only the steps of the procedure are counted: the formula
--   `Alg.pre F fb x` is made in the hand-over. The proof of the lower bound uses F and fb that are
--   computable in polynomial time (`CircuitLowerBound.StForm`, `CircuitLowerBound.StFlip`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/CorENP.lean#L44-L49
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/CorENP.lean#L44-L49

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_ENP
import Definitions.Def_Eight_ViaGrouping_CorDefs2
import Definitions.Def_Eight_ViaGrouping_CorGraph
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_CorENP
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open ENP Groundwork Turing CircuitLowerBound

theorem Eight.ViaGrouping.ALGO_runs_of {En : ℕ → ℕ → ℕ → Paper.StepMachine (List Unit × Groundwork.Prog.Fml) (List Bool)} (h : EngineCounts En) {δ : ℝ} (hδ : 0 < δ) : ∃ ℓ τ c : ℕ, Paper.PolyTimeSteps (En 3 ℓ τ) ∧
    ∀ (a₀ : ℕ) (g : MCode → ℕ) (F : (MCode × List Unit × ℕ) × List GateD → List Unit × Cnf) (fb : List Unit → Bool), Alg.FormOK a₀ g F → ∀ x : List Bool,
      ∃ (T : ℕ) (b : Bool), (Alg.algo (En 3 ℓ τ) F fb).Runs x T (c * ((Alg.pre F fb x).1.length + 2) ^ c) b ∧ (b = true ↔ ¬Sat (Alg.pre F fb x).2) ∧
        (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * (Alg.pre F fb x).1.length) := by sorry
