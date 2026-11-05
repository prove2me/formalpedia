-- Prove2me | Theorems.Thm_CircuitLowerBound_Blocks_obeys_flatMap
-- name    : CircuitLowerBound.Blocks.obeys_flatMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:04:47.839402+00:00
-- url     : https://prove2.me/theorems/9aa8b9fe-18cc-4328-9667-483ca917e49b
-- title:
--   Blocks: obeys flat Map
-- statement:
--   The Blocks construction uses the obeys flat Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L103-L116
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L103-L116

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Blocks
set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Blocks
open ENP Groundwork

theorem CircuitLowerBound.Blocks.obeys_flatMap (v : ℕ → Bool) (n : ℕ) {k : ℕ} (f : ℕ → List GateD) (hf : ∀ i, (f i).length = k) (w : ℕ) :
    Obeys v n ((List.range w).flatMap f) ↔ ∀ i < w, Obeys v (n + k * i) (f i) := by sorry
