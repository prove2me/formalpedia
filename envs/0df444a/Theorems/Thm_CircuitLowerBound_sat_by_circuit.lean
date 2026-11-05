-- Prove2me | Theorems.Thm_CircuitLowerBound_sat_by_circuit
-- name    : CircuitLowerBound.sat_by_circuit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T18:41:46.618355+00:00
-- url     : https://prove2.me/theorems/2b5c80ee-879c-406e-80c0-edf4c78ab2a1
-- title:
--   Circuit Lower Bound: sat by circuit
-- statement:
--   A circuit that decides the language on the words of length m computes a satisfying assignment of
--   `Phi m`, if there is one.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Main.lean#L51-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Main.lean#L51-L59

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Interfaces
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Main
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork Turing

theorem CircuitLowerBound.sat_by_circuit (hG : StGreedy) (hV : StVars) {m : ℕ} {C : Circuit} (hC : ∀ x : List Bool, x.length = m → (eval C x = true ↔ L0 x))
    (hs : Sat (Phi m)) : ∀ D ∈ Phi m, ∃ l ∈ D, eval C (toWord m l.1) = l.2 := by sorry
