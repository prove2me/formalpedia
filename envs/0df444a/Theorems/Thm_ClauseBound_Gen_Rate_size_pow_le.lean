-- Prove2me | Theorems.Thm_ClauseBound_Gen_Rate_size_pow_le
-- name    : ClauseBound.Gen.Rate.size_pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:42:40.522838+00:00
-- url     : https://prove2.me/theorems/71add0c1-1719-4a12-9107-7b61941aa171
-- title:
--   Rate: size pow le
-- statement:
--   size (a^n) ≤ n·size a + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/RateAux.lean#L65-L69
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/RateAux.lean#L65-L69

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

theorem ClauseBound.Gen.Rate.size_pow_le (a n : ℕ) : size (a ^ n) ≤ n * size a + 1 := by sorry
