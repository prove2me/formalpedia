-- Prove2me | Theorems.Thm_ClauseBound_Gen_Rate_nPat_le
-- name    : ClauseBound.Gen.Rate.nPat_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:23:11.297206+00:00
-- url     : https://prove2.me/theorems/8d3b9c17-bf06-4509-8ca6-8b0d046d1fd1
-- title:
--   Rate: n Pat le
-- statement:
--   The number of patterns is at most X^(c·R).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L106-L109
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L106-L109

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

theorem ClauseBound.Gen.Rate.nPat_le (hP : Par P ρ c) (hx : 18 ≤ x₀) (l lam B : ℕ) (hlam : 1 ≤ lam) :
    nPat P (step P x₀ l) lam ≤ (g x₀ l ^ 2 * (lam + B)) ^ (c * nRectG (g x₀ l) (g x₀ l)) := by sorry
