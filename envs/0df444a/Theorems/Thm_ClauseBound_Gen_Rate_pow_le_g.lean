-- Prove2me | Theorems.Thm_ClauseBound_Gen_Rate_pow_le_g
-- name    : ClauseBound.Gen.Rate.pow_le_g
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:44:08.419866+00:00
-- url     : https://prove2.me/theorems/9b1877a0-353d-4374-ab4b-ad242259e07a
-- title:
--   Rate: pow le g
-- statement:
--   2^{ℓ+5} ≤ g_ℓ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L57-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L57-L60

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_RateAux
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_ClauseBound_Gen_Rate
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}

theorem ClauseBound.Gen.Rate.pow_le_g (hx : 18 ≤ x₀) (l : ℕ) : 2 ^ (l + 5) ≤ g x₀ l := by sorry
