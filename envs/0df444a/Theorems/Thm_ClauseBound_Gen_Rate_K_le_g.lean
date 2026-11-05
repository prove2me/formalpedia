-- Prove2me | Theorems.Thm_ClauseBound_Gen_Rate_K_le_g
-- name    : ClauseBound.Gen.Rate.K_le_g
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:16:46.4722+00:00
-- url     : https://prove2.me/theorems/a2835697-fb3c-4635-ab68-2f8dd21292a7
-- title:
--   Rate: K le g
-- statement:
--   K_ℓ ≤ g_ℓ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L53-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Rate.lean#L53-L54

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

theorem ClauseBound.Gen.Rate.K_le_g (x₀ l : ℕ) : K x₀ l ≤ g x₀ l := by sorry
