-- Prove2me | Theorems.Thm_CircuitLowerBound_Alg_runs_algo
-- name    : CircuitLowerBound.Alg.runs_algo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:37:52.994198+00:00
-- url     : https://prove2.me/theorems/6df923cd-a3af-4b85-b9ec-399c9689bceb
-- title:
--   Alg: runs algo
-- statement:
--   The algorithm ends on every input, and its answer is «the formula is unsatisfiable».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Machine.lean#L252-L261
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Machine.lean#L252-L261

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Alg_Parse
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_PaddedDescent_Host
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Alg_Machine
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork Turing Parse
open CircuitLowerBound.Alg
variable {F : (MCode × List Unit × ℕ) × List GateD → List Unit × Cnf} {fb : List Unit → Bool}
variable {a₀ : ℕ} {g : MCode → ℕ}

theorem CircuitLowerBound.Alg.runs_algo {E : Stepped (List Unit × Prog.Fml) (List Bool)} {c : ℕ} {δ : ℝ} (hE : EngineOK E c δ) (hF : FormOK a₀ g F) (x : List Bool) :
    ∃ (T : ℕ) (b : Bool), (algo E F fb).Runs x T (c * ((pre F fb x).1.length + 2) ^ c) b ∧ (b = true ↔ ¬Sat (pre F fb x).2) ∧
      (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * (pre F fb x).1.length) := by sorry
