-- Prove2me | Theorems.Thm_CircuitLowerBound_Blocks_obeys_append
-- name    : CircuitLowerBound.Blocks.obeys_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:03:50.993002+00:00
-- url     : https://prove2.me/theorems/68c0b6c9-7831-4952-aca6-e5463603f861
-- title:
--   Blocks: obeys append
-- statement:
--   The Blocks construction uses the obeys append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L83-L88
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L83-L88

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

theorem CircuitLowerBound.Blocks.obeys_append (v : ℕ → Bool) (n : ℕ) (C D : List GateD) : Obeys v n (C ++ D) ↔ Obeys v n C ∧ Obeys v (n + C.length) D := by sorry
