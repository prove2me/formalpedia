-- Prove2me | Theorems.Thm_ClauseBound_TopN_Arith_Wof_ge
-- name    : ClauseBound.TopN.Arith.Wof_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:20:56.76719+00:00
-- url     : https://prove2.me/theorems/b8fd5f4a-2fc5-4e15-97a8-2c3d1729d215
-- title:
--   Arith: Wof ge
-- statement:
--   What is used of W: it dominates b·D, b²·Y, b·Y and 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Arith.lean#L116-L135
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Arith.lean#L116-L135

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_TopN_Budget
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Definitions.Def_ClauseBound_TopN_Arith
set_option autoImplicit false
section
open ClauseBound ClauseBound.TopN ClauseBound.TopN.Arith
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith
variable {k K n s C₀ : ℕ}

theorem ClauseBound.TopN.Arith.Wof_ge (hK : 1 ≤ K) : (betaN k s + 3) * 2 ^ betaN k s ≤ Wof k K s ∧ (betaN k s + 3) ^ 2 * K.size ≤ Wof k K s ∧
    (betaN k s + 3) ^ 2 ≤ Wof k K s ∧ (betaN k s + 3) * K.size ≤ Wof k K s ∧ K.size ≤ Wof k K s ∧ betaN k s + 3 ≤ Wof k K s ∧ 2 ^ betaN k s ≤ Wof k K s ∧ 1 ≤ Wof k K s := by sorry
