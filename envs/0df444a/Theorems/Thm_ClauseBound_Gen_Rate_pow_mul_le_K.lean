-- Prove2me | Theorems.Thm_ClauseBound_Gen_Rate_pow_mul_le_K
-- name    : ClauseBound.Gen.Rate.pow_mul_le_K
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:23:09.358199+00:00
-- url     : https://prove2.me/theorems/d05af841-7334-4c14-91de-81ca13692d4c
-- title:
--   Rate: pow mul le K
-- statement:
--   2^{x₀}·2^ℓ ≤ K_ℓ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L40-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L40-L42

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

theorem ClauseBound.Gen.Rate.pow_mul_le_K (hx : 18 ≤ x₀) (l : ℕ) : 2 ^ x₀ * 2 ^ l ≤ K x₀ l := by sorry
