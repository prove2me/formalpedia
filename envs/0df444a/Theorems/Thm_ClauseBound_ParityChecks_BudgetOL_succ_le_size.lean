-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_BudgetOL_succ_le_size
-- name    : ClauseBound.ParityChecks.BudgetOL.succ_le_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:45:54.226869+00:00
-- url     : https://prove2.me/theorems/d384cb68-fa21-4427-b0f2-8dfaf0cfa93f
-- title:
--   Budget OL: succ le size
-- statement:
--   n + 1 ≤ 2^(size n).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BudgetOL.lean#L39-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BudgetOL.lean#L39-L39

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

theorem ClauseBound.ParityChecks.BudgetOL.succ_le_size (n : ℕ) : n + 1 ≤ 2 ^ Nat.size n := by sorry
