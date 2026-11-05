-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_BudgetOL_clause_le
-- name    : ClauseBound.ParityChecks.BudgetOL.clause_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:32:25.203141+00:00
-- url     : https://prove2.me/theorems/d9d23ea5-fb77-4d6a-a304-d865dd31d1a4
-- title:
--   Budget OL: clause le
-- statement:
--   The word of a clause: k·(3n+5) + 10 ≤ 2^(k + size n + 4).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BudgetOL.lean#L42-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BudgetOL.lean#L42-L48

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

theorem ClauseBound.ParityChecks.BudgetOL.clause_le (k n : ℕ) : k * (3 * n + 5) + 10 ≤ 2 ^ (k + Nat.size n + 4) := by sorry
