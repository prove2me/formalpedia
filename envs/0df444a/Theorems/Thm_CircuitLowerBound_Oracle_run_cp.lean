-- Prove2me | Theorems.Thm_CircuitLowerBound_Oracle_run_cp
-- name    : CircuitLowerBound.Oracle.run_cp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:44:35.503589+00:00
-- url     : https://prove2.me/theorems/2c2484c4-08fa-4430-a291-30df5b7302fe
-- title:
--   Oracle: run cp
-- statement:
--   The copying loop.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Runs.lean#L102-L128
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Runs.lean#L102-L128

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Oracle_Machine
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Oracle_Runs
import Theorems.Thm_Groundwork_TM_Run_one

set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Oracle
open ENP Turing Groundwork.TM
variable {M : TM2ComputableAux Bool Bool} (O : Lang)

theorem CircuitLowerBound.Oracle.run_cp {s d : NS} (hsd : s ≠ d) {mark : Bool} {me : Ctl} {nx : Λ' M} (hme : prog M (.inr me) = cpS M s d mark (.inr me) nx)
    (hask : me ≠ .ask) (v : M.tm.σ) (l : List Bool) : ∀ (L : List (M.tm.Γ M.tm.k₀)) (n : NS → List Bool), n s = l →
    Run (stp M O) ⟨some (.inr me), (v, none), stk M (one M.tm.k₀ L) n⟩ (l.length + 1)
      ⟨some nx, (v, none), stk M (one M.tm.k₀ (pushed M mark l L)) (Function.update (Function.update n s []) d (l.reverse ++ n d))⟩ := by sorry
