-- Prove2me | Theorems.Thm_ClauseBound_Gen_K_eq
-- name    : ClauseBound.Gen.K_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:32:10.478415+00:00
-- url     : https://prove2.me/theorems/ac4b0d5e-9545-418a-958a-734f95d7c367
-- title:
--   Gen: K eq
-- statement:
--   K_ℓ = 2^{x_ℓ}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/PartA.lean#L28-L31
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/PartA.lean#L28-L31

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

theorem ClauseBound.Gen.K_eq (x₀ l : ℕ) : K x₀ l = 2 ^ x x₀ l := by sorry
