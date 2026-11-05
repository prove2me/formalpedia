-- Prove2me | Theorems.Thm_ClauseBound_Gen_Rate_step_D__34894c
-- name    : ClauseBound.Gen.Rate.step_D
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:15:15.547203+00:00
-- url     : https://prove2.me/theorems/34894c09-58a9-4b06-95e8-7d078a9a9c1e
-- title:
--   Rate: step D
-- statement:
--   The Rate construction uses the step D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L32-L32
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L32-L32

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

theorem ClauseBound.Gen.Rate.step_D (P : PiecesF) (x₀ l : ℕ) : (step P x₀ l).D = 3 * P.m * 2 ^ (l + 4) := by sorry
