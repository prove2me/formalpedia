-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_BudgetOL_nProf_le
-- name    : ClauseBound.ParityChecks.BudgetOL.nProf_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:43:34.596629+00:00
-- url     : https://prove2.me/theorems/ff219c2e-3868-425c-855a-71aba5426690
-- title:
--   Budget OL: n Prof le
-- statement:
--   The list of profiles: (M + 1)^(g·g·3) ≤ 2^(g·g·3·size M).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BudgetOL.lean#L74-L77
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BudgetOL.lean#L74-L77

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

theorem ClauseBound.ParityChecks.BudgetOL.nProf_le (g M : ℕ) : Mark.nProf g M 3 ≤ 2 ^ (g * g * 3 * Nat.size M) := by sorry
