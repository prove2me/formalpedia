-- Prove2me | Theorems.Thm_ClauseBound_Alg_TopArith_sq_mul_lam_le
-- name    : ClauseBound.Alg.TopArith.sq_mul_lam_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:20:53.695105+00:00
-- url     : https://prove2.me/theorems/83c575fc-220c-44ab-8b26-2fcb53557576
-- title:
--   Top Arith: sq mul lam le
-- statement:
--   K²·λ ≤ 8km.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/TopArith.lean#L187-L198
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/TopArith.lean#L187-L198

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

theorem ClauseBound.Alg.TopArith.sq_mul_lam_le (hK : 2 ≤ K) (hk : 1 ≤ k) (hm : K ^ 9 ≤ m) : K ^ 2 * lamTopK K (3 * K ^ 8) k m ≤ 8 * (k * m) := by sorry
