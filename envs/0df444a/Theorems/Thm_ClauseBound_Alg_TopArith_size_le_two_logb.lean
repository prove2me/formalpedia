-- Prove2me | Theorems.Thm_ClauseBound_Alg_TopArith_size_le_two_logb
-- name    : ClauseBound.Alg.TopArith.size_le_two_logb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:11:21.000451+00:00
-- url     : https://prove2.me/theorems/54b1f632-9bff-4dcc-ba24-b3b98215bb58
-- title:
--   Top Arith: size le two logb
-- statement:
--   The number of bits of K ≥ 2 is at most 2·log₂ K.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/TopArith.lean#L105-L112
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/TopArith.lean#L105-L112

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

theorem ClauseBound.Alg.TopArith.size_le_two_logb (K : ℕ) (hK : 2 ≤ K) : (K.size : ℝ) ≤ 2 * Real.logb 2 K := by sorry
