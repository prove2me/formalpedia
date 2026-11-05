-- Prove2me | Theorems.Thm_ClauseBound_Gen_Rate_X_cast
-- name    : ClauseBound.Gen.Rate.X_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:15:57.663305+00:00
-- url     : https://prove2.me/theorems/cfe5e1ee-a2c5-4163-b964-295be2f443f9
-- title:
--   Rate: X cast
-- statement:
--   X as a real number.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L120-L121
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L120-L121

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

theorem ClauseBound.Gen.Rate.X_cast (x₀ l lam B : ℕ) : ((g x₀ l ^ 2 * (lam + B) : ℕ) : ℝ) = (K x₀ (l + 1) : ℝ) * (lam + B) := by sorry
