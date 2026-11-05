-- Prove2me | Theorems.Thm_ClauseBound_Gen_logb_K
-- name    : ClauseBound.Gen.logb_K
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:01:37.056113+00:00
-- url     : https://prove2.me/theorems/d7bc90e3-35e8-4bfc-85a2-d9f37f87fafc
-- title:
--   Gen: logb K
-- statement:
--   log K_ℓ = x_ℓ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/PartA.lean#L44-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/PartA.lean#L44-L45

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

theorem ClauseBound.Gen.logb_K (x₀ l : ℕ) : Real.logb 2 (K x₀ l) = x x₀ l := by sorry
