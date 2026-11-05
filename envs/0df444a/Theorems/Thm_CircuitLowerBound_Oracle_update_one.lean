-- Prove2me | Theorems.Thm_CircuitLowerBound_Oracle_update_one
-- name    : CircuitLowerBound.Oracle.update_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:01:36.965961+00:00
-- url     : https://prove2.me/theorems/6ef6618b-828d-4302-899c-f52d5f372783
-- title:
--   Oracle: update one
-- statement:
--   The Oracle construction uses the update one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Machine.lean#L207-L207
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Machine.lean#L207-L207

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

theorem CircuitLowerBound.Oracle.update_one (k : M.tm.K) (w w' : List (M.tm.Γ k)) : Function.update (one k w) k w' = one k w' := by sorry
