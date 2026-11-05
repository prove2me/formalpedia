-- Prove2me | Theorems.Thm_CircuitLowerBound_Alg_sat_Phi_of_pre
-- name    : CircuitLowerBound.Alg.sat_Phi_of_pre
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:07:51.994477+00:00
-- url     : https://prove2.me/theorems/545ec890-0a19-4841-af03-9e0addc9afa2
-- title:
--   Alg: sat Phi of pre
-- statement:
--   If the formula is unsatisfiable, `Phi m` is satisfiable.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Machine.lean#L141-L159
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Machine.lean#L141-L159

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

theorem CircuitLowerBound.Alg.sat_Phi_of_pre (hF : FormOK a₀ g F) (hb : FlipOK fb) (x : List Bool) (h : ¬Sat (pre F fb x).2) : Sat (Phi (ones x)) := by sorry
