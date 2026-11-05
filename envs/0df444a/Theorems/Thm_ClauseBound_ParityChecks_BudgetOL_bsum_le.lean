-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_BudgetOL_bsum_le
-- name    : ClauseBound.ParityChecks.BudgetOL.bsum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:21:30.941633+00:00
-- url     : https://prove2.me/theorems/8100c91c-d231-44d9-b992-ff66f6e523f7
-- title:
--   Budget OL: bsum le
-- statement:
--   bsum τ k ≤ 2^β.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BudgetOL.lean#L51-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BudgetOL.lean#L51-L55

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_PaddedDescent_F_ArithWalk
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_ClauseBound_ParityChecks_BudgetOL
import Theorems.Thm_WidthK_Thresholds_bsum_le

set_option autoImplicit false
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.BudgetOL
open PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.TopN ClauseBound.ParityChecks
open WidthK (bsum)

theorem ClauseBound.ParityChecks.BudgetOL.bsum_le (k s : ℕ) : bsum (tauOf s) k ≤ 2 ^ betaN k s := by sorry
