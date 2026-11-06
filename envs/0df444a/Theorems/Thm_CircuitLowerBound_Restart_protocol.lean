-- Prove2me | Theorems.Thm_CircuitLowerBound_Restart_protocol
-- name    : CircuitLowerBound.Restart.protocol
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:08:58.136107+00:00
-- url     : https://prove2.me/theorems/ecb5f5ba-8a75-41d9-b239-2b9ebbc0e2e9
-- title:
--   Restart: protocol
-- statement:
--   The protocol, from what the rounds return. After j answers the negated answers are the first j
--   values of the search; d more rounds with a query follow, and the round with the result.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Restart.lean#L59-L75
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Restart.lean#L59-L75

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_ENP_Round
import Definitions.Def_CircuitLowerBound_Small
import Definitions.Def_CountKSatRate_Pad
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_ENP_Restart
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork PaddedDescent Turing
open CircuitLowerBound.Restart
open Classical

theorem CircuitLowerBound.Restart.protocol {N : TM2ComputableAux Bool Bool} {T : ℕ} {x : List Bool} {φ : Cnf}
    (hq : ∀ j ≤ ofWord x, ENP.Round N T x ((greedy φ j).map fun b => !b) (true :: encCnf (φ ++ units (greedy φ j ++ [false]))))
    (hd : ENP.Round N T x ((greedy φ (ofWord x + 1)).map fun b => !b) [false, (greedy φ (ofWord x + 1)).getD (ofWord x) false]) :
    ∀ d j r : ℕ, j + d = ofWord x + 1 → d ≤ r →
      Protocol N T x ((greedy φ (ofWord x + 1)).getD (ofWord x) false) ((greedy φ j).map fun b => !b) r
  := by sorry
