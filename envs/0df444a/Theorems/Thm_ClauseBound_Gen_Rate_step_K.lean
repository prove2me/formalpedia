-- Prove2me | Theorems.Thm_ClauseBound_Gen_Rate_step_K
-- name    : ClauseBound.Gen.Rate.step_K
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:44:43.238798+00:00
-- url     : https://prove2.me/theorems/8d086850-a3b6-4ac6-b4d7-f20131d52f08
-- title:
--   Rate: step K
-- statement:
--   The Rate construction uses the step K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L29-L29
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L29-L29

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

theorem ClauseBound.Gen.Rate.step_K (P : PiecesF) (x₀ l : ℕ) : (step P x₀ l).K = K x₀ l := by sorry
