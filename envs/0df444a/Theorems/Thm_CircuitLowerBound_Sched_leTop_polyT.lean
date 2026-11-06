-- Prove2me | Theorems.Thm_CircuitLowerBound_Sched_leTop_polyT
-- name    : CircuitLowerBound.Sched.leTop_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:03:50.646175+00:00
-- url     : https://prove2.me/theorems/dc061f4c-6c25-47b9-9db6-5a672df8aacb
-- title:
--   Sched: le Top poly T
-- statement:
--   The comparison with the last place of chain a, for a in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/Sched.lean#L80-L85
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/Sched.lean#L80-L85

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

theorem CircuitLowerBound.Sched.leTop_polyT {a s : α → ℕ} (ha : Unary a) (hs : PolyT s) : PolyT fun x => leTop (a x) (s x) := by sorry
