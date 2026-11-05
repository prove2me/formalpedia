-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_ArithOL_argO_le
-- name    : ClauseBound.ParityChecks.ArithOL.argO_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:22:11.592345+00:00
-- url     : https://prove2.me/theorems/b1a8f376-c798-44d2-8ff1-3f7aee8551aa
-- title:
--   Arith OL: arg O le
-- statement:
--   The argument of the logarithm in the bound of the solver: K·(λ + B) ≤ 2^(5·17·C₀·Y + 16).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ArithOL.lean#L95-L135
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ArithOL.lean#L95-L135

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
variable {k K n s C₀ : ℕ}

theorem ClauseBound.ParityChecks.ArithOL.argO_le (hK : 2 ≤ K) (hn17 : K ^ 17 ≤ n) (hlt : n < K ^ (17 * C₀)) (hD : 2 ^ betaN k s ≤ n + 1) :
    K * (lamS K (3 * K ^ 8) (UbOL k K n (2 ^ betaN k s)) (PbOL K n (2 ^ betaN k s)) + bitsS K (3 * K ^ 8) (PbOL K n (2 ^ betaN k s)) 0)
      ≤ 2 ^ (5 * (17 * C₀ * K.size) + 16) := by sorry
