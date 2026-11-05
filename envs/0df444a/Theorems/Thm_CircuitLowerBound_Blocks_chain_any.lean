-- Prove2me | Theorems.Thm_CircuitLowerBound_Blocks_chain_any
-- name    : CircuitLowerBound.Blocks.chain_any
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T18:41:15.099811+00:00
-- url     : https://prove2.me/theorems/d7e9c659-cdad-43d5-8d9b-23027b5debfe
-- title:
--   Blocks: chain any
-- statement:
--   A chain of gates «the wire before, or p i».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L224-L242
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L224-L242

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

theorem CircuitLowerBound.Blocks.chain_any (v : ℕ → Bool) (off init len : ℕ) (p : ℕ → Bool) (h : ∀ i < len, v (off + i) = (v (prevW off init i) || p i)) :
    ∀ m ≤ len, v (prevW off init m) = (v init || decide (∃ i < m, p i = true)) := by sorry
