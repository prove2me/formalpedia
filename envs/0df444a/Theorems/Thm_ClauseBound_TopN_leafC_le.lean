-- Prove2me | Theorems.Thm_ClauseBound_TopN_leafC_le
-- name    : ClauseBound.TopN.leafC_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:09:01.366438+00:00
-- url     : https://prove2.me/theorems/71724ed3-e007-4ac8-aa83-75349a767ed4
-- title:
--   Top N: leaf C le
-- statement:
--   leafC τ k + 2 ≤ 2^β.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Budget.lean#L37-L49
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Budget.lean#L37-L49

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_PaddedDescent_F_ArithWalk
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_ClauseBound_TopN_Budget
set_option autoImplicit false
section
open ClauseBound ClauseBound.TopN
open PaddedDescent PaddedDescent.F CountKSatRate
open WidthK (theta bsum leafC)

theorem ClauseBound.TopN.leafC_le (k s : ℕ) : leafC (tauOf s) k + 2 ≤ 2 ^ betaN k s := by sorry
