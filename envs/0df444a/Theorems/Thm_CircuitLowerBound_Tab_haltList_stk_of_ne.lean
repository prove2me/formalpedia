-- Prove2me | Theorems.Thm_CircuitLowerBound_Tab_haltList_stk_of_ne
-- name    : CircuitLowerBound.Tab.haltList_stk_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:31:47.981729+00:00
-- url     : https://prove2.me/theorems/5d2ccdb4-24e2-4df5-9d58-4c0e217c9973
-- title:
--   Tab: halt List stk of ne
-- statement:
--   The Tab construction uses the halt List stk of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Sound.lean#L39-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Sound.lean#L39-L39

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

theorem CircuitLowerBound.Tab.haltList_stk_of_ne (s : List (N.tm.Γ N.tm.k₁)) {k : N.tm.K} (h : k ≠ N.tm.k₁) : (haltList N.tm s).stk k = [] := by sorry
