-- Prove2me | Theorems.Thm_CircuitLowerBound_Oracle_haltList_stk
-- name    : CircuitLowerBound.Oracle.haltList_stk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:44:09.683625+00:00
-- url     : https://prove2.me/theorems/ce1acec2-7aa9-41e5-88c0-06d88ea43729
-- title:
--   Oracle: halt List stk
-- statement:
--   The Oracle construction uses the halt List stk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Machine.lean#L220-L224
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Machine.lean#L220-L224

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_ToTuring_TM_Run
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Oracle_Machine
import Theorems.Thm_Groundwork_TM_Run_one

set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Oracle
open ENP Turing Groundwork.TM
variable (M : TM2ComputableAux Bool Bool)
variable {M}

theorem CircuitLowerBound.Oracle.haltList_stk (s : List (M.tm.Γ M.tm.k₁)) : (haltList M.tm s).stk = one M.tm.k₁ s := by sorry
