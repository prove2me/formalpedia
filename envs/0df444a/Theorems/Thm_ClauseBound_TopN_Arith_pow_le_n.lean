-- Prove2me | Theorems.Thm_ClauseBound_TopN_Arith_pow_le_n
-- name    : ClauseBound.TopN.Arith.pow_le_n
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:31:04.278104+00:00
-- url     : https://prove2.me/theorems/ed8d58fa-66f0-4f0f-8578-d7e48a848350
-- title:
--   Arith: pow le n
-- statement:
--   Powers of K up to the seventeenth are at most n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Arith.lean#L88-L88
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Arith.lean#L88-L88

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
variable {k K n s : ℕ}

theorem ClauseBound.TopN.Arith.pow_le_n (hK : 1 ≤ K) (hn : K ^ 17 ≤ n) {j : ℕ} (hj : j ≤ 17) : K ^ j ≤ n := by sorry
