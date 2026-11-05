-- Prove2me | Theorems.Thm_ClauseBound_Alg_TopArith_cube_le
-- name    : ClauseBound.Alg.TopArith.cube_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:09:17.801837+00:00
-- url     : https://prove2.me/theorems/8179e808-abbd-4067-930b-6ba1027e8629
-- title:
--   Top Arith: cube le
-- statement:
--   K³ ≤ km.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/TopArith.lean#L181-L184
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/TopArith.lean#L181-L184

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

theorem ClauseBound.Alg.TopArith.cube_le (hK : 2 ≤ K) (hk : 1 ≤ k) (hm : K ^ 9 ≤ m) : K ^ 3 ≤ k * m := by sorry
