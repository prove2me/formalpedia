-- Prove2me | Theorems.Thm_CircuitLowerBound_Round_roundF_polyT
-- name    : CircuitLowerBound.Round.roundF_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:02:55.216066+00:00
-- url     : https://prove2.me/theorems/7bc4b607-b742-4d90-acbc-890149bdc4d9
-- title:
--   Round: round F poly T
-- statement:
--   One round is polynomial-time in the input word and the pad.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Round.lean#L368-L376
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Round.lean#L368-L376

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
variable {G : (MCode × List Unit × ℕ) × List Unit → Cnf} {fb : List Unit → Bool}
variable {α : Type} [Enc α]

theorem CircuitLowerBound.Round.roundF_polyT (h1 : StCertSched) (hG : PolyT G) (hfb : PolyT fb) : PolyT (roundF G fb) := by sorry
