-- Prove2me | Theorems.Thm_CircuitLowerBound_Alg_isZ_binary
-- name    : CircuitLowerBound.Alg.isZ_binary
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:06:55.164093+00:00
-- url     : https://prove2.me/theorems/5a6aa66a-0db4-4f0c-995e-109682074604
-- title:
--   Alg: is Z binary
-- statement:
--   All N + 1 bits of a number below 2^(N+1) are 0 if and only if the number is 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Machine.lean#L227-L243
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Machine.lean#L227-L243

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

theorem CircuitLowerBound.Alg.isZ_binary {N c : ℕ} (h : c < 2 ^ (N + 1)) : isZ (SatK.binary N c) = true ↔ c = 0 := by sorry
