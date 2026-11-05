-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_BudgetOL_le_four
-- name    : ClauseBound.ParityChecks.BudgetOL.le_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:32:26.199562+00:00
-- url     : https://prove2.me/theorems/2b015afe-6c4c-4034-9b09-a2c42f7804cb
-- title:
--   Budget OL: le four
-- statement:
--   Each of four summands is at most the sum.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BudgetOL.lean#L136-L136
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BudgetOL.lean#L136-L136

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

theorem ClauseBound.ParityChecks.BudgetOL.le_four (a b c d : ℕ) : a ≤ a + b + c + d ∧ b ≤ a + b + c + d ∧ c ≤ a + b + c + d ∧ d ≤ a + b + c + d := by sorry
