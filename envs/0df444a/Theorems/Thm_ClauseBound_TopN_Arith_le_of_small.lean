-- Prove2me | Theorems.Thm_ClauseBound_TopN_Arith_le_of_small
-- name    : ClauseBound.TopN.Arith.le_of_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:42:41.477589+00:00
-- url     : https://prove2.me/theorems/662a2e76-f354-43cf-85c6-9aea60525b85
-- title:
--   Arith: le of small
-- statement:
--   If s is below a bound t and 2^(−s) ≤ e, then n ≤ 2^t·(n·e).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/ArithR.lean#L114-L125
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/ArithR.lean#L114-L125

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

theorem ClauseBound.TopN.Arith.le_of_small {s t n : ℕ} {e : ℝ} (hst : s ≤ t) (g1 : 1 / (2 : ℝ) ^ s ≤ e) : (n : ℝ) ≤ ((2 ^ t : ℕ) : ℝ) * ((n : ℝ) * e) := by sorry
