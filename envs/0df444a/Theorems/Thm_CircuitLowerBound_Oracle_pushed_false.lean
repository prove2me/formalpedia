-- Prove2me | Theorems.Thm_CircuitLowerBound_Oracle_pushed_false
-- name    : CircuitLowerBound.Oracle.pushed_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:44:31.937235+00:00
-- url     : https://prove2.me/theorems/c80ad312-3d13-497a-9ec4-43501cd50099
-- title:
--   Oracle: pushed false
-- statement:
--   The Oracle construction uses the pushed false property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Runs.lean#L91-L94
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Runs.lean#L91-L94

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Oracle_Machine
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Oracle_Runs
set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Oracle
open ENP Turing Groundwork.TM
variable {M : TM2ComputableAux Bool Bool} (O : Lang)

theorem CircuitLowerBound.Oracle.pushed_false (l : List Bool) : ∀ L, pushed M false l L = l.reverse.map M.inputAlphabet.invFun ++ L := by sorry
