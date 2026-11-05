-- Prove2me | Theorems.Thm_CircuitLowerBound_Blocks_length_flatMap_const
-- name    : CircuitLowerBound.Blocks.length_flatMap_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:02:13.036555+00:00
-- url     : https://prove2.me/theorems/059f5e03-cad2-455c-9b95-512d18396241
-- title:
--   Blocks: length flat Map const
-- statement:
--   The Blocks construction uses the length flat Map const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L97-L101
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L97-L101

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

theorem CircuitLowerBound.Blocks.length_flatMap_const {α : Type} {k : ℕ} (f : ℕ → List α) (hf : ∀ i, (f i).length = k) (w : ℕ) :
    ((List.range w).flatMap f).length = k * w := by sorry
