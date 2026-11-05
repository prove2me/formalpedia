-- Prove2me | Theorems.Thm_CircuitLowerBound_Sched_fld_polyT
-- name    : CircuitLowerBound.Sched.fld_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:13:01.059479+00:00
-- url     : https://prove2.me/theorems/67ea853d-0906-46d7-b971-f6cb653640b8
-- title:
--   Sched: fld poly T
-- statement:
--   A number of W bits in a word.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/Sched.lean#L93-L94
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/Sched.lean#L93-L94

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

theorem CircuitLowerBound.Sched.fld_polyT {W i : α → ℕ} {w : α → List Bool} (hW : PolyT W) (hw : PolyT w) (hi : PolyT i) : PolyT fun x => fld (W x) (w x) (i x) := by sorry
