-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_ArithOL_le_of_lt_n0
-- name    : ClauseBound.ParityChecks.ArithOL.le_of_lt_n0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:22:32.534587+00:00
-- url     : https://prove2.me/theorems/418a1d73-87e1-40e1-92ef-f60104ec8613
-- title:
--   Arith OL: le of lt n0
-- statement:
--   If n < n₀, then n ≤ n₀^C₀·(n·e), because 1/e ≤ (log₂ K)^C₀ and K ≤ n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ArithOL.lean#L493-L510
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ArithOL.lean#L493-L510

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_ClauseBound_ParityChecks_Sizes
import Definitions.Def_ClauseBound_ParityChecks_ArithAux
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_ClauseBound_TopN_Budget
import Definitions.Def_ClauseBound_Alg_TopArith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_ClauseBound_ParityChecks_ArithOL
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.ArithOL
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.TopN ClauseBound.TopN.Arith

theorem ClauseBound.ParityChecks.ArithOL.le_of_lt_n0 {K n n₀ C₀ : ℕ} {e : ℝ} (hK : 2 ≤ K) (hKn : K ≤ n) (hn : n < n₀) (he : 1 / Real.logb 2 K ^ C₀ ≤ e) :
    (n : ℝ) ≤ ((n₀ ^ C₀ : ℕ) : ℝ) * ((n : ℝ) * e) := by sorry
