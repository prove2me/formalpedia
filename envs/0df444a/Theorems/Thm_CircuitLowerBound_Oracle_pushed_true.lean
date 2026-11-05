-- Prove2me | Theorems.Thm_CircuitLowerBound_Oracle_pushed_true
-- name    : CircuitLowerBound.Oracle.pushed_true
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T18:44:20.328847+00:00
-- url     : https://prove2.me/theorems/2c6b5fb7-506b-492e-96a2-556cbc7d69c7
-- title:
--   Oracle: pushed true
-- statement:
--   The Oracle construction uses the pushed true property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Runs.lean#L96-L99
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Runs.lean#L96-L99

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

theorem CircuitLowerBound.Oracle.pushed_true (l : List Bool) : ∀ L, pushed M true l L = (l.reverse.flatMap fun b => [true, b]).map M.inputAlphabet.invFun ++ L := by sorry
