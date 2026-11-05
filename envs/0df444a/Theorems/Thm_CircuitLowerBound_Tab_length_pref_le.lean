-- Prove2me | Theorems.Thm_CircuitLowerBound_Tab_length_pref_le
-- name    : CircuitLowerBound.Tab.length_pref_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:40:23.611602+00:00
-- url     : https://prove2.me/theorems/3c47954e-4def-45dc-8db5-af9514fb7395
-- title:
--   Tab: length pref le
-- statement:
--   The Tab construction uses the length pref le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Frame.lean#L125-L128
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Frame.lean#L125-L128

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Spec
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Frame
set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Tab
open ENP Turing

theorem CircuitLowerBound.Tab.length_pref_le {α : Type} : ∀ L : List (Option α), (pref L).length ≤ L.length
  := by sorry
