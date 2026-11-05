-- Prove2me | Theorems.Thm_ClauseBound_Gen_K_cast
-- name    : ClauseBound.Gen.K_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:32:14.378314+00:00
-- url     : https://prove2.me/theorems/125fdfca-c371-49e8-88af-4d87545ed06f
-- title:
--   Gen: K cast
-- statement:
--   The real number K_ℓ is 2^{x_ℓ}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/PartA.lean#L40-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/PartA.lean#L40-L41

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_LevelsStatement
import Definitions.Def_ClauseBound_Gen_PartA
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen
open Levels.Gen

theorem ClauseBound.Gen.K_cast (x₀ l : ℕ) : (K x₀ l : ℝ) = 2 ^ x x₀ l := by sorry
