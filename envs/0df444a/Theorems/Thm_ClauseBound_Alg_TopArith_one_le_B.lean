-- Prove2me | Theorems.Thm_ClauseBound_Alg_TopArith_one_le_B
-- name    : ClauseBound.Alg.TopArith.one_le_B
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:10:13.390682+00:00
-- url     : https://prove2.me/theorems/76fbba89-06ab-4819-9646-200347bcc3cd
-- title:
--   Top Arith: one le B
-- statement:
--   The bound for the entries of the top instance is at least 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/TopArith.lean#L207-L212
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/TopArith.lean#L207-L212

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

theorem ClauseBound.Alg.TopArith.one_le_B (hK : 2 ≤ K) : 1 ≤ PtopK (3 * K ^ 8) k m * (2 * (3 * K ^ 8) / K) := by sorry
