-- Prove2me | Theorems.Thm_CircuitLowerBound_Sched_fits_polyT
-- name    : CircuitLowerBound.Sched.fits_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:13:38.635204+00:00
-- url     : https://prove2.me/theorems/600b5bd9-d51f-4502-9483-c350ba4e90ca
-- title:
--   Sched: fits poly T
-- statement:
--   «There is room».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/Sched.lean#L144-L152
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/Sched.lean#L144-L152

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Cert_Sched
set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Sched
open ENP Groundwork
variable {α : Type} [Enc α]

theorem CircuitLowerBound.Sched.fits_polyT {e : α → MCode} {L P : α → ℕ} (he : PolyT e) (hL : Unary L) (hP : PolyT P) : PolyT fun x => decide (Fits (e x) (L x) (P x)) := by sorry
