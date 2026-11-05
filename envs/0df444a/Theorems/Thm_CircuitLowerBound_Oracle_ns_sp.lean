-- Prove2me | Theorems.Thm_CircuitLowerBound_Oracle_ns_sp
-- name    : CircuitLowerBound.Oracle.ns_sp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:00:36.342961+00:00
-- url     : https://prove2.me/theorems/390001df-9e10-4fdb-8ca1-c01d4ec65994
-- title:
--   Oracle: ns sp
-- statement:
--   The Oracle construction uses the ns sp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Machine.lean#L196-L196
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Machine.lean#L196-L196

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_ToTuring_TM_Run
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Oracle_Machine
set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Oracle
open ENP Turing Groundwork.TM
variable (M : TM2ComputableAux Bool Bool)
variable {M}
variable (a b c w : List Bool)

theorem CircuitLowerBound.Oracle.ns_sp : ns a b c .sp = c := by sorry

attribute [defeq] CircuitLowerBound.Oracle.ns_sp
