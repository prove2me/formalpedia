-- Prove2me | Theorems.Thm_ClauseBound_Gen_Rate_size_mul_le
-- name    : ClauseBound.Gen.Rate.size_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:51:37.442829+00:00
-- url     : https://prove2.me/theorems/b0e0c7d4-cfbe-44e8-a5b0-bc3d836b82c8
-- title:
--   Rate: size mul le
-- statement:
--   size (a·b) ≤ size a + size b.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/RateAux.lean#L30-L32
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/RateAux.lean#L30-L32

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

theorem ClauseBound.Gen.Rate.size_mul_le (a b : ℕ) : size (a * b) ≤ size a + size b := by sorry
