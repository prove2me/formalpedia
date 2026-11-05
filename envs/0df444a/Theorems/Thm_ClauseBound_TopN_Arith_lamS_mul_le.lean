-- Prove2me | Theorems.Thm_ClauseBound_TopN_Arith_lamS_mul_le
-- name    : ClauseBound.TopN.Arith.lamS_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:50:11.743196+00:00
-- url     : https://prove2.me/theorems/5c83e700-4db4-4540-afb2-08fff8ad01c7
-- title:
--   Arith: lam S mul le
-- statement:
--   K²·λ·K ≤ K³ + K·Ub + g·P for the label length λ of the rebalanced instance.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Arith.lean#L96-L96
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Arith.lean#L96-L96

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

theorem ClauseBound.TopN.Arith.lamS_mul_le (K g Ub P : ℕ) : lamS K g Ub P * K ^ 3 ≤ K ^ 3 + K * Ub + g * P := by sorry
