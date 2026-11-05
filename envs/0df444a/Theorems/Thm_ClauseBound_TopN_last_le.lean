-- Prove2me | Theorems.Thm_ClauseBound_TopN_last_le
-- name    : ClauseBound.TopN.last_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:08:54.47612+00:00
-- url     : https://prove2.me/theorems/3f2fca11-1e96-41b2-8691-f5bcdeddcfc6
-- title:
--   Top N: last le
-- statement:
--   After 2β + 4 divisions, each of which keeps at most two thirds of the clauses, fewer than n + 2
--   of 2^β·n clauses are left.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Budget.lean#L53-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Budget.lean#L53-L71

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

theorem ClauseBound.TopN.last_le (β : ℕ) {n : ℕ} (hn : 6 ≤ n) : 2 ^ (2 * β + 4) * (2 ^ β * n) + 5 * 3 ^ (2 * β + 4) ≤ 3 ^ (2 * β + 4) * (n + 2) := by sorry
