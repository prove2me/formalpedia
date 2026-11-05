-- Prove2me | Theorems.Thm_CircuitLowerBound_Blocks_prevW_lt
-- name    : CircuitLowerBound.Blocks.prevW_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:28:25.583198+00:00
-- url     : https://prove2.me/theorems/188e2442-6d0e-4c8b-87fd-c26e8f8bf737
-- title:
--   Blocks: prev W lt
-- statement:
--   The Blocks construction uses the prev W lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L200-L201
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L200-L201

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

theorem CircuitLowerBound.Blocks.prevW_lt {off init i : ℕ} (h : init < off) : prevW off init i < off + i := by sorry
