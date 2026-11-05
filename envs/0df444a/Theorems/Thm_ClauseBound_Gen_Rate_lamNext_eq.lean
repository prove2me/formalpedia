-- Prove2me | Theorems.Thm_ClauseBound_Gen_Rate_lamNext_eq
-- name    : ClauseBound.Gen.Rate.lamNext_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:22:26.420658+00:00
-- url     : https://prove2.me/theorems/b3b94253-6c97-47a2-9fa6-48075f11e07f
-- title:
--   Rate: lam Next eq
-- statement:
--   The label length one level down, written out.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L68-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L68-L71

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

theorem ClauseBound.Gen.Rate.lamNext_eq (P : PiecesF) (x₀ l lam : ℕ) : lamNextG P (step P x₀ l) lam =
    (3 * P.m * 2 ^ (l + 4) * (g x₀ l * (g x₀ l - 1) * g x₀ l * lam + nRectG (g x₀ l) (g x₀ l) * capSum P 0 lam) +
      3 * g x₀ l ^ 2 * (g x₀ l ^ 2 * (P.m * lam))) / (3 * P.m * 2 ^ (l + 4) * K x₀ l ^ 2) + 1 := by sorry
