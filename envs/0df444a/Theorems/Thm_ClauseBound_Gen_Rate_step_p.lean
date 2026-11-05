-- Prove2me | Theorems.Thm_ClauseBound_Gen_Rate_step_p
-- name    : ClauseBound.Gen.Rate.step_p
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:36:58.837898+00:00
-- url     : https://prove2.me/theorems/ec305d39-f5b2-423a-b370-540c705d813f
-- title:
--   Rate: step p
-- statement:
--   The Rate construction uses the step p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L30-L30
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L30-L30

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

theorem ClauseBound.Gen.Rate.step_p (P : PiecesF) (x₀ l : ℕ) : (step P x₀ l).p = g x₀ l := by sorry
