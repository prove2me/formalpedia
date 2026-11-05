-- Prove2me | Theorems.Thm_CircuitLowerBound_Oracle_upd_io
-- name    : CircuitLowerBound.Oracle.upd_io
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:01:10.579192+00:00
-- url     : https://prove2.me/theorems/08c3d932-a349-492b-9b89-9ef343d196f2
-- title:
--   Oracle: upd io
-- statement:
--   The Oracle construction uses the upd io property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Machine.lean#L197-L197
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Machine.lean#L197-L197

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

theorem CircuitLowerBound.Oracle.upd_io : Function.update (ns a b c) .io w = ns w b c := by sorry
