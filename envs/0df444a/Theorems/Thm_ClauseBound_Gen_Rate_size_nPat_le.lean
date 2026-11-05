-- Prove2me | Theorems.Thm_ClauseBound_Gen_Rate_size_nPat_le
-- name    : ClauseBound.Gen.Rate.size_nPat_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:16:27.340404+00:00
-- url     : https://prove2.me/theorems/a3cf8919-c67c-4da1-88ea-c38a20c9b451
-- title:
--   Rate: size n Pat le
-- statement:
--   A crude bound on the bit length of the number of patterns.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L112-L117
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L112-L117

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

theorem ClauseBound.Gen.Rate.size_nPat_le (hP : Par P ρ c) (l lam : ℕ) (hlam : 1 ≤ lam) :
    Nat.size (nPat P (step P x₀ l) lam) ≤ nRectG (g x₀ l) (g x₀ l) * (2 * lam) ^ c + 1 := by sorry
