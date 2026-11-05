-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_ArithOL_real_finalO
-- name    : ClauseBound.ParityChecks.ArithOL.real_finalO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:23:04.249645+00:00
-- url     : https://prove2.me/theorems/39c829dc-825c-4f75-b7a5-23f582e9177c
-- title:
--   Arith OL: real final O
-- statement:
--   The main term and the rest, in terms of n·e·(s+1).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ArithOL.lean#L321-L333
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ArithOL.lean#L321-L333

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

theorem ClauseBound.ParityChecks.ArithOL.real_finalO {e n k b ck q cA Z R3 N : ℝ} (he0 : 0 ≤ e) (hn0 : 0 ≤ n) (hk0 : 0 ≤ k) (hq : 1 ≤ q) (hcA : 0 ≤ cA)
    (rb : b ≤ ck * q) (hZ : Z ≤ e * (354 * k * n * b) + cA * (n * e)) (hR3 : R3 ≤ n * e) (hN : N ≤ Z + R3) :
    N ≤ (354 * k * ck + cA + 1) * n * e * q := by sorry
