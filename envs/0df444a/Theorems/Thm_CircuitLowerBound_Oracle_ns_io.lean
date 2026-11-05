-- Prove2me | Theorems.Thm_CircuitLowerBound_Oracle_ns_io
-- name    : CircuitLowerBound.Oracle.ns_io
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:58:42.940189+00:00
-- url     : https://prove2.me/theorems/e4078f1e-d806-4e49-af9e-4900399dcd6b
-- title:
--   Oracle: ns io
-- statement:
--   The Oracle construction uses the ns io property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Machine.lean#L194-L194
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Machine.lean#L194-L194

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

theorem CircuitLowerBound.Oracle.ns_io : ns a b c .io = a := by sorry

attribute [defeq] CircuitLowerBound.Oracle.ns_io
