-- Prove2me | Theorems.Thm_ClauseBound_TopN_Arith_b_le_D
-- name    : ClauseBound.TopN.Arith.b_le_D
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:34:59.455057+00:00
-- url     : https://prove2.me/theorems/d27bbfc3-20c0-4c48-b23e-3cbdbef3dd6d
-- title:
--   Arith: b le D
-- statement:
--   β + 3 ≤ 2^β.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Arith.lean#L71-L76
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Arith.lean#L71-L76

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

theorem ClauseBound.TopN.Arith.b_le_D (k s : ℕ) : betaN k s + 3 ≤ 2 ^ betaN k s := by sorry
