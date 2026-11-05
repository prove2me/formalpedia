-- Prove2me | Theorems.Thm_ClauseBound_Gen_Rate_size_eight_mul_le
-- name    : ClauseBound.Gen.Rate.size_eight_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:23:07.875612+00:00
-- url     : https://prove2.me/theorems/5292b27e-89bb-4568-a247-891ab527c829
-- title:
--   Rate: size eight mul le
-- statement:
--   size (8·a) ≤ size a + 3.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/RateAux.lean#L54-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/RateAux.lean#L54-L57

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

theorem ClauseBound.Gen.Rate.size_eight_mul_le (a : ℕ) : size (8 * a) ≤ size a + 3 := by sorry
