-- Prove2me | Theorems.Thm_ClauseBound_Gen_Rate_bNext_eq
-- name    : ClauseBound.Gen.Rate.bNext_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:23:30.262354+00:00
-- url     : https://prove2.me/theorems/da3f2160-5750-44d6-b866-b5a0b192062b
-- title:
--   Rate: b Next eq
-- statement:
--   B', written out.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L136-L139
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L136-L139

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

theorem ClauseBound.Gen.Rate.bNext_eq (P : PiecesF) (x₀ l lam B : ℕ) : bNextG P (step P x₀ l) lam B =
    P.m * (g x₀ l * g x₀ l ^ 2 * lam) * (2 * g x₀ l / K x₀ l) +
      (g x₀ l * B + g x₀ l ^ 2 * P.bits 0 lam) * (2 * g x₀ l / K x₀ l + 2 * g x₀ l / K x₀ l * (2 * g x₀ l / K x₀ l)) * K x₀ l := by sorry
