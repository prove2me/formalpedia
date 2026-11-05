-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_ArithOL_planAtO_getD_le
-- name    : ClauseBound.ParityChecks.ArithOL.planAtO_getD_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:21:29.248672+00:00
-- url     : https://prove2.me/theorems/7a18653d-e2ae-49b7-8c9a-d83843018127
-- title:
--   Arith OL: plan At O get D le
-- statement:
--   The exponent of a plan, or else n, is at most n; and at most `needO` if the five tests are
--   passed.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ArithOL.lean#L426-L457
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ArithOL.lean#L426-L457

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

theorem ClauseBound.ParityChecks.ArithOL.planAtO_getD_le {Idx : Type} [Enc Idx] {S : Solver Idx} (hS : S.Poly) (c n₀ k n : ℕ) (i : Idx) (s : ℕ) :
    (planAtO S c n₀ k n i s).getD n ≤ n ∧
      ((s0K k ≤ s ∧ 2 ^ betaN k s ≤ n + 1 ∧ n₀ ≤ n ∧ 2 ^ betaN k s ≤ (Nat.log 2 n + 1) ^ c ∧ 2 * LD (2 ^ betaN k s) ≤ n) →
        (planAtO S c n₀ k n i s).getD n ≤ needO S k i n s) := by sorry
