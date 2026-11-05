-- Prove2me | Theorems.Thm_ClauseBound_Gen_Rate_two_lam_le
-- name    : ClauseBound.Gen.Rate.two_lam_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:00:22.088204+00:00
-- url     : https://prove2.me/theorems/aa40a25c-044b-45d0-b869-77f8c81c952a
-- title:
--   Rate: two lam le
-- statement:
--   2λ ≤ g²·(λ + B).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L92-L99
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L92-L99

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

theorem ClauseBound.Gen.Rate.two_lam_le (hx : 18 ≤ x₀) (l lam B : ℕ) : 2 * lam ≤ g x₀ l ^ 2 * (lam + B) := by sorry
