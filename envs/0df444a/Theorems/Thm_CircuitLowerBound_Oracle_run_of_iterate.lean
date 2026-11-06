-- Prove2me | Theorems.Thm_CircuitLowerBound_Oracle_run_of_iterate
-- name    : CircuitLowerBound.Oracle.run_of_iterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:44:07.789296+00:00
-- url     : https://prove2.me/theorems/368e8834-9b4b-4b59-b08a-79a1bf5e7a57
-- title:
--   Oracle: run of iterate
-- statement:
--   Mathlib's form of a run, read back.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Machine.lean#L271-L287
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Machine.lean#L271-L287

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

theorem CircuitLowerBound.Oracle.run_of_iterate {C : Type} {f : C → Option C} : ∀ {t : ℕ} {a b : C}, (flip bind f)^[t] (some a) = some b → Run f a t b
  := by sorry
