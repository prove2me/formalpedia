-- Prove2me | Theorems.Thm_ClauseBound_Alg_TopArith_two_g_div
-- name    : ClauseBound.Alg.TopArith.two_g_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:36:23.120776+00:00
-- url     : https://prove2.me/theorems/c9f94afe-e6c3-4593-b6bc-a3525072d732
-- title:
--   Top Arith: two g div
-- statement:
--   2g/K = 6K⁷.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/TopArith.lean#L162-L164
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/TopArith.lean#L162-L164

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

theorem ClauseBound.Alg.TopArith.two_g_div (hK : 2 ≤ K) : 2 * (3 * K ^ 8) / K = 6 * K ^ 7 := by sorry
