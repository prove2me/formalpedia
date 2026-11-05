-- Prove2me | Theorems.Thm_ClauseBound_Alg_TopArith_le_logb_of_pow_le
-- name    : ClauseBound.Alg.TopArith.le_logb_of_pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:35:51.67534+00:00
-- url     : https://prove2.me/theorems/29762842-73f0-415d-98a7-d72b372688f5
-- title:
--   Top Arith: le logb of pow le
-- statement:
--   n ≤ log₂ x if 2ⁿ ≤ x.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/TopArith.lean#L99-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/TopArith.lean#L99-L102

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_ClauseBound_Alg_TopArith
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.TopArith
open PaddedDescent.F

theorem ClauseBound.Alg.TopArith.le_logb_of_pow_le (x n : ℕ) (h : 2 ^ n ≤ x) : (n : ℝ) ≤ Real.logb 2 x := by sorry
