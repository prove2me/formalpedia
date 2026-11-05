-- Prove2me | Theorems.Thm_CircuitLowerBound_Tab_haltList_stk_self
-- name    : CircuitLowerBound.Tab.haltList_stk_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:14:48.173221+00:00
-- url     : https://prove2.me/theorems/dae380ca-b079-4b3c-b83d-e4c4e737a80f
-- title:
--   Tab: halt List stk self
-- statement:
--   The Tab construction uses the halt List stk self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Sound.lean#L37-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Sound.lean#L37-L37

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Frame
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Sound
set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Tab
open ENP Turing
variable (N : TM2ComputableAux Bool Bool)

theorem CircuitLowerBound.Tab.haltList_stk_self (s : List (N.tm.Γ N.tm.k₁)) : (haltList N.tm s).stk N.tm.k₁ = s := by sorry
