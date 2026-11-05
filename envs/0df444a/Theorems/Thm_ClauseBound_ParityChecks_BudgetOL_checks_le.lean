-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_BudgetOL_checks_le
-- name    : ClauseBound.ParityChecks.BudgetOL.checks_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:20:33.387973+00:00
-- url     : https://prove2.me/theorems/971c0dca-9ff6-4ca8-978e-7316050579bf
-- title:
--   Budget OL: checks le
-- statement:
--   The lists of the checks: 8(6n+1)(m+1)(size m + 2) + 8 ≤ 2^(3·size m + 3·size n + 12).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BudgetOL.lean#L80-L92
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BudgetOL.lean#L80-L92

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

theorem ClauseBound.ParityChecks.BudgetOL.checks_le (n m : ℕ) : 8 * (6 * n + 1) * (m + 1) * (Nat.size m + 2) + 8 ≤ 2 ^ (3 * Nat.size m + 3 * Nat.size n + 12) := by sorry
