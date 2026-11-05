-- Prove2me | Theorems.Thm_CircuitLowerBound_Oracle_stk_inr
-- name    : CircuitLowerBound.Oracle.stk_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:58:17.20368+00:00
-- url     : https://prove2.me/theorems/e3a1eb1a-442b-424d-848a-7edcd2b6ac96
-- title:
--   Oracle: stk inr
-- statement:
--   The Oracle construction uses the stk inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Machine.lean#L166-L166
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Machine.lean#L166-L166

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

theorem CircuitLowerBound.Oracle.stk_inr (T : ∀ k, List (M.tm.Γ k)) (n : NS → List Bool) (j : NS) : stk M T n (.inr j) = n j := by sorry

attribute [defeq] CircuitLowerBound.Oracle.stk_inr
