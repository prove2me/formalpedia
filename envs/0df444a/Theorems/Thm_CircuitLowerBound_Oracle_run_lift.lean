-- Prove2me | Theorems.Thm_CircuitLowerBound_Oracle_run_lift
-- name    : CircuitLowerBound.Oracle.run_lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:44:07.145668+00:00
-- url     : https://prove2.me/theorems/203b6b6d-2f21-4462-8942-8fb1d5deeaa8
-- title:
--   Oracle: run lift
-- statement:
--   A run of M is a run of the new machine of the same length; where M halts, the new machine is at
--   `after`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Machine.lean#L260-L268
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Machine.lean#L260-L268

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

theorem CircuitLowerBound.Oracle.run_lift (O : Lang) (n : NS → List Bool) :
    ∀ {t : ℕ} {a b : TM2.Cfg M.tm.Γ M.tm.Λ M.tm.σ}, Run (TM2.step M.tm.m) a t b → Run (stp M O) (liftCfg n a) t (liftCfg n b)
  := by sorry
