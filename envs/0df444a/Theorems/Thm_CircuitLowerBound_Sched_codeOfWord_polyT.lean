-- Prove2me | Theorems.Thm_CircuitLowerBound_Sched_codeOfWord_polyT
-- name    : CircuitLowerBound.Sched.codeOfWord_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:03:47.921577+00:00
-- url     : https://prove2.me/theorems/ed5b109c-2c71-441f-958a-d4f4a9b367d1
-- title:
--   Sched: code Of Word poly T
-- statement:
--   The table written by a word.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/Sched.lean#L107-L120
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/Sched.lean#L107-L120

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

theorem CircuitLowerBound.Sched.codeOfWord_polyT {u : α → List Bool} (hu : PolyT u) : PolyT fun x => codeOfWord (u x) := by sorry
