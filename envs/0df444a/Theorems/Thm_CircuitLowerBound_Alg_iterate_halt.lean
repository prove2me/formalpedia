-- Prove2me | Theorems.Thm_CircuitLowerBound_Alg_iterate_halt
-- name    : CircuitLowerBound.Alg.iterate_halt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:08:05.275667+00:00
-- url     : https://prove2.me/theorems/5f17adc7-41a4-49c1-84b8-ec661f68178c
-- title:
--   Alg: iterate halt
-- statement:
--   From a halted configuration there is no step.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Machine.lean#L290-L294
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Machine.lean#L290-L294

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Alg_Parse
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_PaddedDescent_Host
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Alg_Machine
import Theorems.Thm_WidthK_InvK_step

set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork Turing Parse
open CircuitLowerBound.Alg
variable {F : (MCode × List Unit × ℕ) × List GateD → List Unit × Cnf} {fb : List Unit → Bool}
variable {a₀ : ℕ} {g : MCode → ℕ}

theorem CircuitLowerBound.Alg.iterate_halt (tm : FinTM2) (o : List (tm.Γ tm.k₁)) (k : ℕ) :
    (flip bind tm.step)^[k + 1] (some (haltList tm o)) = none := by sorry
