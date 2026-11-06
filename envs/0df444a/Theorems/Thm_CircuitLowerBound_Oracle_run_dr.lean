-- Prove2me | Theorems.Thm_CircuitLowerBound_Oracle_run_dr
-- name    : CircuitLowerBound.Oracle.run_dr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:44:14.823472+00:00
-- url     : https://prove2.me/theorems/df43cd74-c594-44e0-9a65-f86eedccada2
-- title:
--   Oracle: run dr
-- statement:
--   The loop that empties the stack s.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Runs.lean#L67-L84
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Runs.lean#L67-L84

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

theorem CircuitLowerBound.Oracle.run_dr {s : NS} {me : Ctl} {nx : Λ' M} (hme : prog M (.inr me) = drS M s (.inr me) nx) (hask : me ≠ .ask)
    (v : M.tm.σ) (T : ∀ k, List (M.tm.Γ k)) (l : List Bool) : ∀ n : NS → List Bool, n s = l →
    Run (stp M O) ⟨some (.inr me), (v, none), stk M T n⟩ (l.length + 1) ⟨some nx, (v, none), stk M T (Function.update n s [])⟩ := by sorry
