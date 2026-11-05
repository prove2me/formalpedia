-- Prove2me | Theorems.Thm_ClauseBound_TopN_Arith_master
-- name    : ClauseBound.TopN.Arith.master
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:22:42.535106+00:00
-- url     : https://prove2.me/theorems/c1b4fc31-035a-423d-9c70-d4d69570181d
-- title:
--   Arith: master
-- statement:
--   W ≤ A₁·K·e.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/ArithR.lean#L66-L104
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/ArithR.lean#L66-L104

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_Alg_TopArith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Definitions.Def_ClauseBound_TopN_ArithR
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open ClauseBound ClauseBound.TopN ClauseBound.TopN.Arith
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith

theorem ClauseBound.TopN.Arith.master {K s C C₀ k : ℕ} {e : ℝ} (hK : 2 ≤ K) (he : 1 / Real.logb 2 K ^ C₀ ≤ e) (h2 : (2 : ℝ) ^ s ≤ (2 / e) ^ C) :
    ((Wof k K s : ℕ) : ℝ) ≤ (A1 k C C₀ : ℝ) * K * e := by sorry
