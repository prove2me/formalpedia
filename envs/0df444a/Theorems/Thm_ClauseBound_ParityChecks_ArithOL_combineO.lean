-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_ArithOL_combineO
-- name    : ClauseBound.ParityChecks.ArithOL.combineO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:22:34.075162+00:00
-- url     : https://prove2.me/theorems/057ca732-1553-4436-8672-4d0a296a1509
-- title:
--   Arith OL: combine O
-- statement:
--   The cases together.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ArithOL.lean#L513-L529
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ArithOL.lean#L513-L529

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

theorem ClauseBound.ParityChecks.ArithOL.combineO {p n e q B c A d : ℝ} (hn : 0 ≤ n) (he : 0 ≤ e) (hq : 1 ≤ q) (hB : 0 ≤ B) (hc : 0 ≤ c) (hA : 0 ≤ A) (hd : 0 ≤ d)
    (h : p ≤ B * n * e * q ∨ p ≤ c * (n * e) ∨ p ≤ A * (n * e) ∨ p ≤ d * (n * e)) : p ≤ (B + c + A + d) * n * e * q := by sorry
