-- Prove2me | Theorems.Thm_ClauseBound_Alg_TopArith_logb_pow_le
-- name    : ClauseBound.Alg.TopArith.logb_pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:20:35.100059+00:00
-- url     : https://prove2.me/theorems/35395993-5b76-4a10-91a8-8642dbebb016
-- title:
--   Top Arith: logb pow le
-- statement:
--   (log₂ K)ⁿ ≤ n!·2ⁿ·K.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/TopArith.lean#L115-L132
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/TopArith.lean#L115-L132

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

theorem ClauseBound.Alg.TopArith.logb_pow_le (K n : ℕ) (hK : 2 ≤ K) : Real.logb 2 K ^ n ≤ (n.factorial * 2 ^ n : ℕ) * (K : ℝ) := by sorry
