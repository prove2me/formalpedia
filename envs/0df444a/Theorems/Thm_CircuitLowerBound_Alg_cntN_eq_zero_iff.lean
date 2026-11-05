-- Prove2me | Theorems.Thm_CircuitLowerBound_Alg_cntN_eq_zero_iff
-- name    : CircuitLowerBound.Alg.cntN_eq_zero_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:06:50.935715+00:00
-- url     : https://prove2.me/theorems/2fd3041f-5f5e-43cd-b78c-a91ba70536f6
-- title:
--   Alg: cnt N eq zero iff
-- statement:
--   The number of satisfying assignments is 0 if and only if the formula is unsatisfiable.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Machine.lean#L208-L217
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Machine.lean#L208-L217

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Alg_Parse
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_PaddedDescent_Host
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Alg_Machine
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork Turing Parse
open CircuitLowerBound.Alg
variable {F : (MCode × List Unit × ℕ) × List GateD → List Unit × Cnf} {fb : List Unit → Bool}
variable {a₀ : ℕ} {g : MCode → ℕ}

theorem CircuitLowerBound.Alg.cntN_eq_zero_iff {N : ℕ} {ψ : Cnf} (h : ∀ D ∈ ψ, ∀ l ∈ D, l.1 < N) : CountKSat.cntN N ψ = 0 ↔ ¬Sat ψ := by sorry
