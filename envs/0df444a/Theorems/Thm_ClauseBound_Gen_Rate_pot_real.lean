-- Prove2me | Theorems.Thm_ClauseBound_Gen_Rate_pot_real
-- name    : ClauseBound.Gen.Rate.pot_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:24:10.885367+00:00
-- url     : https://prove2.me/theorems/bcd979ea-9cd8-4bea-9ea1-a7b5cca475a2
-- title:
--   Rate: pot real
-- statement:
--   The bit length of z + Nat.size cnt one level down.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L163-L178
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L163-L178

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

theorem ClauseBound.Gen.Rate.pot_real (hP : Par P ρ c) (hx : 18 ≤ x₀) (l lam B cnt z : ℕ) (hlam : 1 ≤ lam) :
    (Nat.size (z + nRectG (g x₀ l) (g x₀ l) * Nat.size (P.d 0 lam) + Nat.size (cnt * nPat P (step P x₀ l) lam) + (g x₀ l * g x₀ l) ^ 2 * lam +
      g x₀ l ^ 2 * (g x₀ l * B + g x₀ l ^ 2 * P.bits 0 lam + 1) + 2 + Nat.size (cnt * nPat P (step P x₀ l) lam)) : ℝ) ≤
      Nat.size (z + Nat.size cnt) + 1 + ((c + 3) * Real.logb 2 ((K x₀ (l + 1) : ℝ) * (lam + B)) + 1) := by sorry
