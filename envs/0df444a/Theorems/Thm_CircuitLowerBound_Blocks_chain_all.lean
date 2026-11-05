-- Prove2me | Theorems.Thm_CircuitLowerBound_Blocks_chain_all
-- name    : CircuitLowerBound.Blocks.chain_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:34:57.987113+00:00
-- url     : https://prove2.me/theorems/75d318b4-884a-48c7-b8c0-13f3ecac68f9
-- title:
--   Blocks: chain all
-- statement:
--   A chain of gates «the wire before, and p i».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L204-L221
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L204-L221

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

theorem CircuitLowerBound.Blocks.chain_all (v : ℕ → Bool) (off init len : ℕ) (p : ℕ → Bool) (h : ∀ i < len, v (off + i) = (v (prevW off init i) && p i)) :
    ∀ m ≤ len, v (prevW off init m) = (v init && decide (∀ i < m, p i = true)) := by sorry
