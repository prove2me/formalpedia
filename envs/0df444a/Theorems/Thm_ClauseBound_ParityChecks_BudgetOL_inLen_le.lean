-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_BudgetOL_inLen_le
-- name    : ClauseBound.ParityChecks.BudgetOL.inLen_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:32:36.626611+00:00
-- url     : https://prove2.me/theorems/b6aab74b-8b1e-480d-8261-effa377d959d
-- title:
--   Budget OL: in Len le
-- statement:
--   The length of the code of an instance: inLen k n ≤ 2^(3k + 1 + (k+1)·size n).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BudgetOL.lean#L58-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BudgetOL.lean#L58-L71

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

theorem ClauseBound.ParityChecks.BudgetOL.inLen_le (k n : ℕ) : inLen k n ≤ 2 ^ (3 * k + 1 + (k + 1) * Nat.size n) := by sorry
