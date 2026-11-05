-- Prove2me | Theorems.Thm_ClauseBound_Alg_TopArith_g_mul_P_le
-- name    : ClauseBound.Alg.TopArith.g_mul_P_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:34:29.163667+00:00
-- url     : https://prove2.me/theorems/4f0c901e-350e-4357-b609-d30bb2cd7b01
-- title:
--   Top Arith: g mul P le
-- statement:
--   g·P ≤ 5km.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/TopArith.lean#L140-L159
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/TopArith.lean#L140-L159

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
variable {K k m : ℕ}

theorem ClauseBound.Alg.TopArith.g_mul_P_le (hK : 2 ≤ K) (hk : 1 ≤ k) (hm : K ^ 9 ≤ m) : 3 * K ^ 8 * PtopK (3 * K ^ 8) k m ≤ 5 * (k * m) := by sorry
