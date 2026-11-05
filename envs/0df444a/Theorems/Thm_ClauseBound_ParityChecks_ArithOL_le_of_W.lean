-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_ArithOL_le_of_W
-- name    : ClauseBound.ParityChecks.ArithOL.le_of_W
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:22:34.058375+00:00
-- url     : https://prove2.me/theorems/cb2aedaf-a5d0-4605-a9bc-414854fcd678
-- title:
--   Arith OL: le of W
-- statement:
--   If n ≤ W, then n ≤ A₁·(n·e), by the master inequality.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ArithOL.lean#L484-L490
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ArithOL.lean#L484-L490

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

theorem ClauseBound.ParityChecks.ArithOL.le_of_W {k K n s A₁ : ℕ} {e : ℝ} (hKn : K ≤ n) (he0 : 0 ≤ e) (hnW : n ≤ Wof k K s)
    (hM : ((Wof k K s : ℕ) : ℝ) ≤ (A₁ : ℝ) * K * e) : (n : ℝ) ≤ (A₁ : ℝ) * ((n : ℝ) * e) := by sorry
