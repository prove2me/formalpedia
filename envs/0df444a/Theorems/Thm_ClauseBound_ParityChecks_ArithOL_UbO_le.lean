-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_ArithOL_UbO_le
-- name    : ClauseBound.ParityChecks.ArithOL.UbO_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:43:19.552911+00:00
-- url     : https://prove2.me/theorems/36e6bd91-7bdd-4354-b310-9b3528d6ccd4
-- title:
--   Arith OL: Ub O le
-- statement:
--   Ub ≤ 354·k·n·(β+1) + 54·K^16.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ArithOL.lean#L54-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ArithOL.lean#L54-L58

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
variable {k K n s C₀ : ℕ}

theorem ClauseBound.ParityChecks.ArithOL.UbO_le (hn : 1 ≤ n) : UbOL k K n (2 ^ betaN k s) ≤ 354 * k * n * (betaN k s + 1) + 54 * K ^ 16 := by sorry
