-- Prove2me | Theorems.Thm_ClauseBound_Gen_Rate_size_cast_le
-- name    : ClauseBound.Gen.Rate.size_cast_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:43:56.262497+00:00
-- url     : https://prove2.me/theorems/ac86ff24-d13c-4ae8-9ca1-0f6125a867c4
-- title:
--   Rate: size cast le
-- statement:
--   If n ≤ X^k then size n ≤ k·log X + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/RateAux.lean#L72-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/RateAux.lean#L72-L82

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Gen_RateAux
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Rate
open Nat (size)

theorem ClauseBound.Gen.Rate.size_cast_le {n X k : ℕ} (hX : 1 ≤ X) (h : n ≤ X ^ k) : (size n : ℝ) ≤ k * Real.logb 2 X + 1 := by sorry
