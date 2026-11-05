-- Prove2me | Theorems.Thm_CircuitLowerBound_Parse_rest_unary_append
-- name    : CircuitLowerBound.Parse.rest_unary_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:33:07.084326+00:00
-- url     : https://prove2.me/theorems/3653d416-2bd1-46f8-b34c-3c1c2b4b5a01
-- title:
--   Parse: rest unary append
-- statement:
--   What follows 1^P 0 in 1^P 0 y.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Parse.lean#L58-L62
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Parse.lean#L58-L62

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Alg_Parse
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Parse

theorem CircuitLowerBound.Parse.rest_unary_append (P : ℕ) (y : List Bool) : rest (unary P ++ y) = y := by sorry
