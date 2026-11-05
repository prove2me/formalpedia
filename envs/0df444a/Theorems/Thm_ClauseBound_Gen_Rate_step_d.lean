-- Prove2me | Theorems.Thm_ClauseBound_Gen_Rate_step_d
-- name    : ClauseBound.Gen.Rate.step_d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:37:05.659958+00:00
-- url     : https://prove2.me/theorems/d5fb65d6-6403-4958-991e-7203a977e36a
-- title:
--   Rate: step d
-- statement:
--   The Rate construction uses the step d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L31-L31
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L31-L31

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

theorem ClauseBound.Gen.Rate.step_d (P : PiecesF) (x₀ l : ℕ) : (step P x₀ l).d = g x₀ l := by sorry
