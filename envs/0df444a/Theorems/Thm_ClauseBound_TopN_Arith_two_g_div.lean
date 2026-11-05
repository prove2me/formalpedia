-- Prove2me | Theorems.Thm_ClauseBound_TopN_Arith_two_g_div
-- name    : ClauseBound.TopN.Arith.two_g_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:49:35.818541+00:00
-- url     : https://prove2.me/theorems/fe4d5580-96dd-43a4-a35c-cc20d4dddd58
-- title:
--   Arith: two g div
-- statement:
--   2g/K = 6K⁷.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Arith.lean#L91-L93
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Arith.lean#L91-L93

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
import Theorems.Thm_ClauseBound_Alg_TopArith_two_g_div

set_option autoImplicit false
section
open ClauseBound ClauseBound.TopN ClauseBound.TopN.Arith
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith
variable {k K n s : ℕ}

theorem ClauseBound.TopN.Arith.two_g_div (hK : 1 ≤ K) : 2 * (3 * K ^ 8) / K = 6 * K ^ 7 := by sorry
