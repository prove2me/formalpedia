-- Prove2me | Theorems.Thm_ClauseBound_Alg_TopArith_logb_le_of_le_pow
-- name    : ClauseBound.Alg.TopArith.logb_le_of_le_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:49:16.976926+00:00
-- url     : https://prove2.me/theorems/1aff970c-44cf-4ede-a4ca-223bd3ab7fd3
-- title:
--   Top Arith: logb le of le pow
-- statement:
--   log₂ x ≤ n if x ≤ 2ⁿ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/TopArith.lean#L92-L96
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/TopArith.lean#L92-L96

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

theorem ClauseBound.Alg.TopArith.logb_le_of_le_pow (x n : ℕ) (hx : 1 ≤ x) (h : x ≤ 2 ^ n) : Real.logb 2 x ≤ n := by sorry
