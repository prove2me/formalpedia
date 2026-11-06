-- Prove2me | Theorems.Thm_CircuitLowerBound_Tab_holdsC_taut
-- name    : CircuitLowerBound.Tab.holdsC_taut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:43:12.690506+00:00
-- url     : https://prove2.me/theorems/a3870f10-ea7b-48cd-b058-0fd0ad908be8
-- title:
--   Tab: holds C taut
-- statement:
--   The Tab construction uses the holds C taut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Table.lean#L52-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Table.lean#L52-L55

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Frame
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Table
set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Tab
open ENP Turing
variable (N : TM2ComputableAux Bool Bool)
variable {N}

theorem CircuitLowerBound.Tab.holdsC_taut (α : Atom N → ℕ → ℕ → Bool) (b Q P : ℕ) : HoldsC α b Q P taut := by sorry
