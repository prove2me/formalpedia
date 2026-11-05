-- Prove2me | Theorems.Thm_ClauseBound_Gen_Rate_pow_le_K
-- name    : ClauseBound.Gen.Rate.pow_le_K
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:43:58.503602+00:00
-- url     : https://prove2.me/theorems/ec66cb00-999b-481e-8f8d-b8aa9ed4bc94
-- title:
--   Rate: pow le K
-- statement:
--   2^{x₀} ≤ K_ℓ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L45-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L45-L46

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

theorem ClauseBound.Gen.Rate.pow_le_K (hx : 18 ≤ x₀) (l : ℕ) : 2 ^ x₀ ≤ K x₀ l := by sorry
