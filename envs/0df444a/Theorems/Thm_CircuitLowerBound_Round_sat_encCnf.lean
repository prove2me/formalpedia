-- Prove2me | Theorems.Thm_CircuitLowerBound_Round_sat_encCnf
-- name    : CircuitLowerBound.Round.sat_encCnf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:58:57.306015+00:00
-- url     : https://prove2.me/theorems/d69b52e0-6035-46c5-a1d9-433c28d05c80
-- title:
--   Round: sat enc Cnf
-- statement:
--   The code of a formula is in SAT if and only if the formula is satisfiable.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Round.lean#L201-L202
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Round.lean#L201-L202

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_PaddedDescent_Pad
import Definitions.Def_ToTuring_Poly_Decode
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_ENP_Round
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Round

theorem CircuitLowerBound.Round.sat_encCnf (φ : Cnf) : SAT (encCnf φ) ↔ Sat φ := by sorry
