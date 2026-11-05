-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_ArithOL_needO_le_sum
-- name    : ClauseBound.ParityChecks.ArithOL.needO_le_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:22:59.463238+00:00
-- url     : https://prove2.me/theorems/db48167a-020a-4680-b3d5-5d7ebc9c3b0f
-- title:
--   Arith OL: need O le sum
-- statement:
--   The exponent as a sum of its parts.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ArithOL.lean#L339-L357
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ArithOL.lean#L339-L357

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

theorem ClauseBound.ParityChecks.ArithOL.needO_le_sum {Idx : Type} [Enc Idx] (S : Solver Idx) (i : Idx) {k n s : ℕ} (hD : 2 ^ betaN k s ≤ n + 1) :
    needO S k i n s ≤ 3 * S.K i ^ 8 * (S.K i).size + PbOL (S.K i) n (2 ^ betaN k s) * (2 * (3 * S.K i ^ 8) / S.K i + 1) +
      (S.K i - 1) * lamS (S.K i) (3 * S.K i ^ 8) (UbOL k (S.K i) n (2 ^ betaN k s)) (PbOL (S.K i) n (2 ^ betaN k s)) +
      S.need (i, List.replicate (lamS (S.K i) (3 * S.K i ^ 8) (UbOL k (S.K i) n (2 ^ betaN k s)) (PbOL (S.K i) n (2 ^ betaN k s))) (),
        List.replicate (bitsS (S.K i) (3 * S.K i ^ 8) (PbOL (S.K i) n (2 ^ betaN k s)) 0) ()) +
      3 * S.K i ^ 8 * (3 * S.K i ^ 8) * 3 * Nat.size (blkOL (2 ^ betaN k s) * (7 * n + 1)) +
      ((3 * Nat.size (2 ^ betaN k s * n) + 3 * n.size + 12) + 2 + (betaN k s + 5 * k + 10 + (k + 3) * n.size)) + n / 2 ^ s := by sorry
