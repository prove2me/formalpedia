-- Prove2me | Theorems.Thm_CircuitLowerBound_Alg_pre_cases
-- name    : CircuitLowerBound.Alg.pre_cases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:08:09.171863+00:00
-- url     : https://prove2.me/theorems/86908cf1-6029-4db0-83be-ed3f570917eb
-- title:
--   Alg: pre cases
-- statement:
--   The six cases of the definition.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Machine.lean#L74-L97
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Machine.lean#L74-L97

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

theorem CircuitLowerBound.Alg.pre_cases (F : (MCode × List Unit × ℕ) × List GateD → List Unit × Cnf) (fb : List Unit → Bool) (x : List Bool) :
    (pos (ones x) < top (nu (ones x)) ∧ Fits (codeOf (nu (ones x))) (ones x) (next (ones x)) ∧ WF (ones x) (decC (rest x)) ∧
        pre F fb x = F ((codeOf (nu (ones x)), List.replicate (ones x) (), next (ones x)), decC (rest x))) ∨
    (pos (ones x) < top (nu (ones x)) ∧ Fits (codeOf (nu (ones x))) (ones x) (next (ones x)) ∧ ¬WF (ones x) (decC (rest x)) ∧ pre F fb x = ([], [])) ∨
    (pos (ones x) < top (nu (ones x)) ∧ ¬Fits (codeOf (nu (ones x))) (ones x) (next (ones x)) ∧ pre F fb x = ([], [[]])) ∨
    (pos (ones x) = top (nu (ones x)) ∧ fb (List.replicate (ones x) ()) = true ∧ pre F fb x = ([], [])) ∨
    (pos (ones x) = top (nu (ones x)) ∧ fb (List.replicate (ones x) ()) = false ∧ pre F fb x = ([], [[]])) ∨
    (top (nu (ones x)) < pos (ones x) ∧ pre F fb x = ([], [[]])) := by sorry
