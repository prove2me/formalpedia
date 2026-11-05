-- Prove2me | Theorems.Thm_CircuitLowerBound_Tab_initList_stk_of_ne
-- name    : CircuitLowerBound.Tab.initList_stk_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:14:42.728385+00:00
-- url     : https://prove2.me/theorems/d81466bc-3f4f-4d92-a03a-215a6b1e7b82
-- title:
--   Tab: init List stk of ne
-- statement:
--   The Tab construction uses the init List stk of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Sound.lean#L35-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Sound.lean#L35-L35

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

theorem CircuitLowerBound.Tab.initList_stk_of_ne (s : List (N.tm.Γ N.tm.k₀)) {k : N.tm.K} (h : k ≠ N.tm.k₀) : (initList N.tm s).stk k = [] := by sorry
