-- Prove2me | Theorems.Thm_CircuitLowerBound_Alg_outputs_unique
-- name    : CircuitLowerBound.Alg.outputs_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:36:30.897006+00:00
-- url     : https://prove2.me/theorems/7f176cb8-96e8-47e7-8055-190a517a271f
-- title:
--   Alg: outputs unique
-- statement:
--   Two runs of a machine on the same input that end with an output end with the same output.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Machine.lean#L297-L313
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Machine.lean#L297-L313

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

theorem CircuitLowerBound.Alg.outputs_unique {tm : FinTM2} {l : List (tm.Γ tm.k₀)} {o o' : List (tm.Γ tm.k₁)} {T T' : ℕ}
    (h : TM2OutputsInTime tm l (some o) T) (h' : TM2OutputsInTime tm l (some o') T') : o = o' := by sorry
