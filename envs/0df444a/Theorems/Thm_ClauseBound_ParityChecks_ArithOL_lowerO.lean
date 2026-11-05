-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_ArithOL_lowerO
-- name    : ClauseBound.ParityChecks.ArithOL.lowerO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:21:22.667095+00:00
-- url     : https://prove2.me/theorems/b4ae9eb2-b060-4435-971c-cfe1ab186190
-- title:
--   Arith OL: lower O
-- statement:
--   The parts of lower order of the exponent, each multiplied by K.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ArithOL.lean#L138-L241
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ArithOL.lean#L138-L241

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

theorem ClauseBound.ParityChecks.ArithOL.lowerO (hK : 2 ≤ K) (hn17 : K ^ 17 ≤ n) (hlt : n < K ^ (17 * C₀)) :
    K * (3 * K ^ 8 * K.size) ≤ 3 * (Wof k K s * n) ∧
    K * (PbOL K n (2 ^ betaN k s) * (2 * (3 * K ^ 8) / K + 1)) ≤ 3 * GO C₀ * (Wof k K s * n) ∧
    K * ((K - 1) * lamS K (3 * K ^ 8) (UbOL k K n (2 ^ betaN k s)) (PbOL K n (2 ^ betaN k s))) ≤ (55 + 354 * k + GO C₀) * (Wof k K s * n) ∧
    3 * K ^ 8 * PbOL K n (2 ^ betaN k s) ≤ GO C₀ * (Wof k K s * n) ∧
    K * (54 * K ^ 16) ≤ 54 * (Wof k K s * n) ∧
    K * K ^ 2 ≤ Wof k K s * n ∧
    K * (C₀ * K ^ 2 * (5 * (17 * C₀ * K.size) + 16)) ≤ C₀ * (85 * C₀ + 16) * (Wof k K s * n) ∧
    K * (3 * K ^ 8 * (3 * K ^ 8) * 3 * Nat.size (blkOL (2 ^ betaN k s) * (7 * n + 1))) ≤ 27 * (4 + 17 * C₀) * (Wof k K s * n) ∧
    K * ((3 * Nat.size (2 ^ betaN k s * n) + 3 * n.size + 12) + 2 + (betaN k s + 5 * k + 10 + (k + 3) * n.size)) ≤ (17 + 51 * C₀) * (Wof k K s * n) := by sorry
