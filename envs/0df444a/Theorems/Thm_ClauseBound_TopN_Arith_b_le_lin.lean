-- Prove2me | Theorems.Thm_ClauseBound_TopN_Arith_b_le_lin
-- name    : ClauseBound.TopN.Arith.b_le_lin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:09:19.998886+00:00
-- url     : https://prove2.me/theorems/d3cd07b7-b7a5-4d63-957e-65c06ad95bdf
-- title:
--   Arith: b le lin
-- statement:
--   β + 3 ≤ c_k·(s+1).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Arith.lean#L79-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Arith.lean#L79-L82

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

theorem ClauseBound.TopN.Arith.b_le_lin (k s : ℕ) : betaN k s + 3 ≤ (17 * (2 ^ (k + 1) + 1) + k + 6) * (s + 1) := by sorry
