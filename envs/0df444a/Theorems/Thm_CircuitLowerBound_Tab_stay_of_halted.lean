-- Prove2me | Theorems.Thm_CircuitLowerBound_Tab_stay_of_halted
-- name    : CircuitLowerBound.Tab.stay_of_halted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:31:49.236889+00:00
-- url     : https://prove2.me/theorems/cb21903a-82f2-43f8-b9b2-b067034c8cd0
-- title:
--   Tab: stay of halted
-- statement:
--   The Tab construction uses the stay of halted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Frame.lean#L206-L209
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Frame.lean#L206-L209

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
variable (N : TM2ComputableAux Bool Bool)

theorem CircuitLowerBound.Tab.stay_of_halted {c : N.tm.Cfg} (h : c.l = none) : stay N c = c := by sorry
