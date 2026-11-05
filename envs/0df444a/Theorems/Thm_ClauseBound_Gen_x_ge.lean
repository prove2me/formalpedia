-- Prove2me | Theorems.Thm_ClauseBound_Gen_x_ge
-- name    : ClauseBound.Gen.x_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:01:42.274645+00:00
-- url     : https://prove2.me/theorems/7b169a28-fb9b-40c4-b2dc-811254ff451f
-- title:
--   Gen: x ge
-- statement:
--   x_ℓ ≥ x₀ + 2ℓ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/PartA.lean#L34-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/PartA.lean#L34-L37

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

theorem ClauseBound.Gen.x_ge (x₀ l : ℕ) (hx : 18 ≤ x₀) : x₀ + 2 * l ≤ x x₀ l := by sorry
