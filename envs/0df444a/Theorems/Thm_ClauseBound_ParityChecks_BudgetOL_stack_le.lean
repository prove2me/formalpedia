-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_BudgetOL_stack_le
-- name    : ClauseBound.ParityChecks.BudgetOL.stack_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:44:50.029004+00:00
-- url     : https://prove2.me/theorems/e01a35e5-edcd-4746-93cf-1acab08f0c49
-- title:
--   Budget OL: stack le
-- statement:
--   The stack of the walk.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BudgetOL.lean#L95-L133
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BudgetOL.lean#L95-L133

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_PaddedDescent_F_ArithWalk
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_ClauseBound_ParityChecks_BudgetOL
set_option autoImplicit false
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.BudgetOL
open PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.TopN ClauseBound.ParityChecks
open WidthK (bsum)

theorem ClauseBound.ParityChecks.BudgetOL.stack_le {k : ℕ} (hk : 1 ≤ k) (n s : ℕ) : stackLenC k (tauOf s) n (inLen k n) ≤ 2 ^ (betaN k s + 5 * k + 10 + (k + 3) * Nat.size n) := by sorry
