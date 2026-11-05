-- Prove2me | Theorems.Thm_CircuitLowerBound_Blocks_ofWord_append
-- name    : CircuitLowerBound.Blocks.ofWord_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:29:26.051506+00:00
-- url     : https://prove2.me/theorems/289fe55b-ad75-4622-a5b1-3c7c2841b5e4
-- title:
--   Blocks: of Word append
-- statement:
--   The Blocks construction uses the of Word append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L249-L252
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L249-L252

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

theorem CircuitLowerBound.Blocks.ofWord_append (l₁ l₂ : List Bool) : ofWord (l₁ ++ l₂) = ofWord l₁ + 2 ^ l₁.length * ofWord l₂ := by sorry
