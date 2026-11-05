-- Prove2me | Theorems.Thm_CircuitLowerBound_Blocks_wfa_append
-- name    : CircuitLowerBound.Blocks.wfa_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:02:42.76544+00:00
-- url     : https://prove2.me/theorems/f0298f04-42a3-49c6-8193-105e275bbeb8
-- title:
--   Blocks: wfa append
-- statement:
--   The Blocks construction uses the wfa append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L90-L95
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L90-L95

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

theorem CircuitLowerBound.Blocks.wfa_append (n : ℕ) (C D : List GateD) : WFa n (C ++ D) ↔ WFa n C ∧ WFa (n + C.length) D := by sorry
