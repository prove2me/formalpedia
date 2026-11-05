-- Prove2me | Theorems.Thm_CircuitLowerBound_Alg_exists_guess
-- name    : CircuitLowerBound.Alg.exists_guess
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:08:03.027317+00:00
-- url     : https://prove2.me/theorems/7ea886ca-1514-4e4d-995c-3162c6a45cb6
-- title:
--   Alg: exists guess
-- statement:
--   If a circuit computes a satisfying assignment of `Phi m`, then for the code y of this circuit
--   the formula is unsatisfiable and has few variables.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Machine.lean#L163-L203
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Machine.lean#L163-L203

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

theorem CircuitLowerBound.Alg.exists_guess (hF : FormOK a₀ g F) (hb : FlipOK fb) (hN : StNorm) {m : ℕ} (hm : 1 ≤ m) (hpos : pos m ≤ top (nu m)) (C : Circuit)
    (hC : ∀ D ∈ Phi m, ∃ l ∈ D, eval C (toWord m l.1) = l.2) :
    ∃ y : List Bool, y.length = (m + C.length) + 1 + C.length * (4 + 2 * (m + C.length)) ∧ ¬Sat (pre F fb (unary m ++ y)).2 ∧
      (pre F fb (unary m ++ y)).1.length ≤ 3 * C.length + a₀ * (m + 1) + g (codeOf (nu m)) := by sorry
