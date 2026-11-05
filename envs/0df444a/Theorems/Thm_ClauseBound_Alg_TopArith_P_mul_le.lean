-- Prove2me | Theorems.Thm_ClauseBound_Alg_TopArith_P_mul_le
-- name    : ClauseBound.Alg.TopArith.P_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:20:43.714309+00:00
-- url     : https://prove2.me/theorems/33ad75b8-2527-4535-bb1d-c12d892a5031
-- title:
--   Top Arith: P mul le
-- statement:
--   P·(2g/K + 1)·K ≤ 15km.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/TopArith.lean#L167-L178
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/TopArith.lean#L167-L178

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

theorem ClauseBound.Alg.TopArith.P_mul_le (hK : 2 ≤ K) (hk : 1 ≤ k) (hm : K ^ 9 ≤ m) :
    PtopK (3 * K ^ 8) k m * (2 * (3 * K ^ 8) / K + 1) * K ≤ 15 * (k * m) := by sorry
