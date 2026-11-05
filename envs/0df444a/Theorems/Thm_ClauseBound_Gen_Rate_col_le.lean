-- Prove2me | Theorems.Thm_ClauseBound_Gen_Rate_col_le
-- name    : ClauseBound.Gen.Rate.col_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:22:48.983431+00:00
-- url     : https://prove2.me/theorems/dde27d4f-afca-43c2-8f4c-cb70ef77f13e
-- title:
--   Rate: col le
-- statement:
--   The budget of the colourings: g·Nat.size K ≤ g⁴.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L187-L194
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L187-L194

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

theorem ClauseBound.Gen.Rate.col_le (hx : 18 ≤ x₀) (l : ℕ) : ((g x₀ l * Nat.size (K x₀ l) : ℕ) : ℝ) ≤ (g x₀ l : ℝ) ^ 4 := by sorry
