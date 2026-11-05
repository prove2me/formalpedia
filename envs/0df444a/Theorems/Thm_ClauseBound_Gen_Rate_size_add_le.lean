-- Prove2me | Theorems.Thm_ClauseBound_Gen_Rate_size_add_le
-- name    : ClauseBound.Gen.Rate.size_add_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:14:58.70365+00:00
-- url     : https://prove2.me/theorems/2f404521-e666-408a-bc49-0fce0bf5b3c2
-- title:
--   Rate: size add le
-- statement:
--   size (a + b) ≤ size a + size b.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/RateAux.lean#L35-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/RateAux.lean#L35-L45

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

theorem ClauseBound.Gen.Rate.size_add_le (a b : ℕ) : size (a + b) ≤ size a + size b := by sorry
