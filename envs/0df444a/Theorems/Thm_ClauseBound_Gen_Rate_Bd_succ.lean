-- Prove2me | Theorems.Thm_ClauseBound_Gen_Rate_Bd_succ
-- name    : ClauseBound.Gen.Rate.Bd_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:22:43.494498+00:00
-- url     : https://prove2.me/theorems/2816c9dd-4d5d-4328-ad5d-d71e3662c130
-- title:
--   Rate: Bd succ
-- statement:
--   The bound at level ℓ + 1 in terms of g_ℓ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L181-L184
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L181-L184

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

theorem ClauseBound.Gen.Rate.Bd_succ (ρ : ℝ) (c x₀ l lam B : ℕ) : Bd ρ c x₀ (l + 1) lam B = e ρ x₀ (l + 1) * ((g x₀ l : ℝ) ^ 4 * lam) +
    (6 * c + 14) * (g x₀ l : ℝ) ^ 4 * Real.logb 2 ((K x₀ (l + 1) : ℝ) * (lam + B)) := by sorry
