-- Prove2me | Theorems.Thm_CircuitLowerBound_Blocks_wfa_map
-- name    : CircuitLowerBound.Blocks.wfa_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:29:26.542807+00:00
-- url     : https://prove2.me/theorems/5bf175cd-5b6d-4054-887f-06615e6c2407
-- title:
--   Blocks: wfa map
-- statement:
--   The Blocks construction uses the wfa map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L142-L144
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L142-L144

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

theorem CircuitLowerBound.Blocks.wfa_map (n : ℕ) (g : ℕ → GateD) (w : ℕ) : WFa n ((List.range w).map g) ↔ ∀ i < w, (g i).2.1 < n + i ∧ (g i).2.2 < n + i := by sorry
