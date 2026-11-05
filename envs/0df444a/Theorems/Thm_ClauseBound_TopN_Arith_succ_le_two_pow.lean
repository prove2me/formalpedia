-- Prove2me | Theorems.Thm_ClauseBound_TopN_Arith_succ_le_two_pow
-- name    : ClauseBound.TopN.Arith.succ_le_two_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:35:14.348203+00:00
-- url     : https://prove2.me/theorems/4defc603-ead0-48bd-96da-4f3091ca460d
-- title:
--   Arith: succ le two pow
-- statement:
--   n + 1 ≤ 2^(17·C₀·Y).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Arith.lean#L138-L142
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Arith.lean#L138-L142

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

theorem ClauseBound.TopN.Arith.succ_le_two_pow (hlt : n < K ^ (17 * C₀)) : n + 1 ≤ 2 ^ (17 * C₀ * K.size) := by sorry
