-- Prove2me | Theorems.Thm_ClauseBound_Gen_Rate_one_le_log
-- name    : ClauseBound.Gen.Rate.one_le_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:44:43.604423+00:00
-- url     : https://prove2.me/theorems/36419a93-b1d9-40e4-9389-2bbea2cce256
-- title:
--   Rate: one le log
-- statement:
--   1 ≤ log(K_ℓ·(λ + B)).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L80-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L80-L87

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

theorem ClauseBound.Gen.Rate.one_le_log (hx : 18 ≤ x₀) (l lam B : ℕ) (hlam : 1 ≤ lam) : 1 ≤ Real.logb 2 ((K x₀ l : ℝ) * (lam + B)) := by sorry
