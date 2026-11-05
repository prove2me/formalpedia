-- Prove2me | Theorems.Thm_CircuitLowerBound_Blocks_wfa_flatMap
-- name    : CircuitLowerBound.Blocks.wfa_flatMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:04:42.889458+00:00
-- url     : https://prove2.me/theorems/35f4d526-40be-4263-8806-68083a4c3e5f
-- title:
--   Blocks: wfa flat Map
-- statement:
--   The Blocks construction uses the wfa flat Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L118-L131
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L118-L131

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

theorem CircuitLowerBound.Blocks.wfa_flatMap (n : ℕ) {k : ℕ} (f : ℕ → List GateD) (hf : ∀ i, (f i).length = k) (w : ℕ) :
    WFa n ((List.range w).flatMap f) ↔ ∀ i < w, WFa (n + k * i) (f i) := by sorry
