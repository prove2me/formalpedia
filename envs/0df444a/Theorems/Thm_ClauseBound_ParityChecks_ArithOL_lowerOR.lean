-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_ArithOL_lowerOR
-- name    : ClauseBound.ParityChecks.ArithOL.lowerOR
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:22:26.151942+00:00
-- url     : https://prove2.me/theorems/11a0992e-70eb-45b7-8658-2ca946efefeb
-- title:
--   Arith OL: lower OR
-- statement:
--   The inequalities of `lowerO` between real numbers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ArithOL.lean#L248-L270
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ArithOL.lean#L248-L270

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

theorem ClauseBound.ParityChecks.ArithOL.lowerOR {k K n s C₀ : ℕ} (hK : 2 ≤ K) (hn17 : K ^ 17 ≤ n) (hlt : n < K ^ (17 * C₀)) :
    (K : ℝ) * ((3 * K ^ 8 * K.size : ℕ) : ℝ) ≤ 3 * (((Wof k K s : ℕ) : ℝ) * n) ∧
    (K : ℝ) * ((PbOL K n (2 ^ betaN k s) * (2 * (3 * K ^ 8) / K + 1) : ℕ) : ℝ) ≤ ((3 * GO C₀ : ℕ) : ℝ) * (((Wof k K s : ℕ) : ℝ) * n) ∧
    (K : ℝ) * (((K - 1) * lamS K (3 * K ^ 8) (UbOL k K n (2 ^ betaN k s)) (PbOL K n (2 ^ betaN k s)) : ℕ) : ℝ) ≤
      ((55 + 354 * k + GO C₀ : ℕ) : ℝ) * (((Wof k K s : ℕ) : ℝ) * n) ∧
    ((3 * K ^ 8 * PbOL K n (2 ^ betaN k s) : ℕ) : ℝ) ≤ (GO C₀ : ℝ) * (((Wof k K s : ℕ) : ℝ) * n) ∧
    (K : ℝ) * ((54 * K ^ 16 : ℕ) : ℝ) ≤ 54 * (((Wof k K s : ℕ) : ℝ) * n) ∧
    (K : ℝ) * (K : ℝ) ^ 2 ≤ ((Wof k K s : ℕ) : ℝ) * n ∧
    (K : ℝ) * ((C₀ : ℝ) * (K : ℝ) ^ 2 * ((5 * (17 * C₀ * K.size) + 16 : ℕ) : ℝ)) ≤ ((C₀ * (85 * C₀ + 16) : ℕ) : ℝ) * (((Wof k K s : ℕ) : ℝ) * n) ∧
    (K : ℝ) * ((3 * K ^ 8 * (3 * K ^ 8) * 3 * Nat.size (blkOL (2 ^ betaN k s) * (7 * n + 1)) : ℕ) : ℝ) ≤ ((27 * (4 + 17 * C₀) : ℕ) : ℝ) * (((Wof k K s : ℕ) : ℝ) * n) ∧
    (K : ℝ) * (((3 * Nat.size (2 ^ betaN k s * n) + 3 * n.size + 12) + 2 + (betaN k s + 5 * k + 10 + (k + 3) * n.size) : ℕ) : ℝ) ≤
      ((17 + 51 * C₀ : ℕ) : ℝ) * (((Wof k K s : ℕ) : ℝ) * n) := by sorry
