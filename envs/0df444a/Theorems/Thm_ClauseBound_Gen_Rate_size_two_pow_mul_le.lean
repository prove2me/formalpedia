-- Prove2me | Theorems.Thm_ClauseBound_Gen_Rate_size_two_pow_mul_le
-- name    : ClauseBound.Gen.Rate.size_two_pow_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:23:39.426214+00:00
-- url     : https://prove2.me/theorems/d2ff3111-97bd-43d5-8864-9c1ebf3128d6
-- title:
--   Rate: size two pow mul le
-- statement:
--   size (2^k·b) ≤ k + 1 + size b.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/RateAux.lean#L60-L62
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/RateAux.lean#L60-L62

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

theorem ClauseBound.Gen.Rate.size_two_pow_mul_le (k b : ℕ) : size (2 ^ k * b) ≤ k + 1 + size b := by sorry
