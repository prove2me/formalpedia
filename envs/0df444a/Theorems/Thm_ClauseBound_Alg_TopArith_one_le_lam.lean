-- Prove2me | Theorems.Thm_ClauseBound_Alg_TopArith_one_le_lam
-- name    : ClauseBound.Alg.TopArith.one_le_lam
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:20:36.4912+00:00
-- url     : https://prove2.me/theorems/95358a50-53f2-4d6c-9ee1-a34fb90de7ad
-- title:
--   Top Arith: one le lam
-- statement:
--   λ ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/TopArith.lean#L201-L204
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/TopArith.lean#L201-L204

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

theorem ClauseBound.Alg.TopArith.one_le_lam (hK : 2 ≤ K) : 1 ≤ lamTopK K (3 * K ^ 8) k m := by sorry
