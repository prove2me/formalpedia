-- Prove2me | Theorems.Thm_ClauseBound_Gen_Pick_pow_le_K
-- name    : ClauseBound.Gen.Pick.pow_le_K
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:47:37.134197+00:00
-- url     : https://prove2.me/theorems/97847002-8320-4f88-be7a-13ec722c1eb8
-- title:
--   Pick: pow le K
-- statement:
--   2^{3ℓ+x₀} ≤ 8·K_ℓ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Pick.lean#L45-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Pick.lean#L45-L53

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Gen_Pick
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Pick
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen

theorem ClauseBound.Gen.Pick.pow_le_K (x₀ l : ℕ) : 2 ^ (3 * l + x₀) ≤ 8 * K x₀ l := by sorry
