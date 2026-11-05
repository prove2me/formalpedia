-- Prove2me | Theorems.Thm_ClauseBound_Gen_Rate_big_le_K
-- name    : ClauseBound.Gen.Rate.big_le_K
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:57:47.494889+00:00
-- url     : https://prove2.me/theorems/b261ed8e-ef00-4bb6-a009-034886fedbba
-- title:
--   Rate: big le K
-- statement:
--   2^18 ≤ K_ℓ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L49-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L49-L50

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

theorem ClauseBound.Gen.Rate.big_le_K (hx : 18 ≤ x₀) (l : ℕ) : 2 ^ 18 ≤ K x₀ l := by sorry
