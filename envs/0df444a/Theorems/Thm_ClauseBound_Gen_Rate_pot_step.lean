-- Prove2me | Theorems.Thm_ClauseBound_Gen_Rate_pot_step
-- name    : ClauseBound.Gen.Rate.pot_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:24:03.090068+00:00
-- url     : https://prove2.me/theorems/79532c3d-97f4-4c50-bd9b-847f7c846d1a
-- title:
--   Rate: pot step
-- statement:
--   How Nat.size (z + Nat.size cnt) grows at one level.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L124-L129
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L124-L129

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

theorem ClauseBound.Gen.Rate.pot_step (z cnt nP a b d : ℕ) :
    Nat.size (z + a + Nat.size (cnt * nP) + b + d + 2 + Nat.size (cnt * nP)) ≤ Nat.size (z + Nat.size cnt) + 1 + Nat.size (a + b + d + 2 + 2 * Nat.size nP) := by sorry
