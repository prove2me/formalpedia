-- Prove2me | Theorems.Thm_ClauseBound_Gen_Rate_four_nRect_le
-- name    : ClauseBound.Gen.Rate.four_nRect_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:39:45.150351+00:00
-- url     : https://prove2.me/theorems/7eb80339-2877-4422-84bb-e8d7558771ce
-- title:
--   Rate: four n Rect le
-- statement:
--   4·(number of rectangles) ≤ g⁴.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/RateAux.lean#L129-L137
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/RateAux.lean#L129-L137

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

theorem ClauseBound.Gen.Rate.four_nRect_le (g : ℕ) : 4 * ClauseBound.Alg.nRectG g g ≤ g ^ 4 := by sorry
