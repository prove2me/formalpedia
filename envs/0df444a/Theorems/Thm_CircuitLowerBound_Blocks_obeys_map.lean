-- Prove2me | Theorems.Thm_CircuitLowerBound_Blocks_obeys_map
-- name    : CircuitLowerBound.Blocks.obeys_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:29:27.714899+00:00
-- url     : https://prove2.me/theorems/fd05dfa3-73e1-435b-af6f-d0474909b9aa
-- title:
--   Blocks: obeys map
-- statement:
--   The Blocks construction uses the obeys map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L138-L140
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L138-L140

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

theorem CircuitLowerBound.Blocks.obeys_map (v : ℕ → Bool) (n : ℕ) (g : ℕ → GateD) (w : ℕ) : Obeys v n ((List.range w).map g) ↔ ∀ i < w, v (n + i) = gval v (g i) := by sorry
