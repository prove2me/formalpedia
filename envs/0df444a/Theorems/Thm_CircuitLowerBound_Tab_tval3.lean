-- Prove2me | Theorems.Thm_CircuitLowerBound_Tab_tval3
-- name    : CircuitLowerBound.Tab.tval3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:38:13.566766+00:00
-- url     : https://prove2.me/theorems/6f4115f7-2fca-4ff8-b732-cee8ce8d10dc
-- title:
--   Tab: tval3
-- statement:
--   The Tab construction uses the tval3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Table.lean#L47-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Table.lean#L47-L47

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

theorem CircuitLowerBound.Tab.tval3 (b t : ℕ) : tval b t 3 = 2 ^ b := by sorry
