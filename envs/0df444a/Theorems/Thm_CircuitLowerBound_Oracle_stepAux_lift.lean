-- Prove2me | Theorems.Thm_CircuitLowerBound_Oracle_stepAux_lift
-- name    : CircuitLowerBound.Oracle.stepAux_lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:44:06.18779+00:00
-- url     : https://prove2.me/theorems/6789da65-a5a1-4d82-9636-9a416ab3ef93
-- title:
--   Oracle: step Aux lift
-- statement:
--   The Oracle construction uses the step Aux lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Machine.lean#L247-L256
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Machine.lean#L247-L256

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

theorem CircuitLowerBound.Oracle.stepAux_lift (n : NS → List Bool) (q : TM2.Stmt M.tm.Γ M.tm.Λ M.tm.σ) (v : M.tm.σ) (T : ∀ k, List (M.tm.Γ k)) :
    TM2.stepAux (lift M q) (v, none) (stk M T n) = liftCfg n (TM2.stepAux q v T) := by sorry
