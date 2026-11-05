-- Prove2me | Theorems.Thm_ClauseBound_Gen_Rate_nPat_eq
-- name    : ClauseBound.Gen.Rate.nPat_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:34:13.580113+00:00
-- url     : https://prove2.me/theorems/7b9f6b64-53ed-47f5-8160-d07ad3beb3a7
-- title:
--   Rate: n Pat eq
-- statement:
--   The number of patterns, written out.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L102-L103
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L102-L103

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

theorem ClauseBound.Gen.Rate.nPat_eq (P : PiecesF) (x₀ l lam : ℕ) : nPat P (step P x₀ l) lam = P.cnt 0 lam ^ nRectG (g x₀ l) (g x₀ l) := by sorry
