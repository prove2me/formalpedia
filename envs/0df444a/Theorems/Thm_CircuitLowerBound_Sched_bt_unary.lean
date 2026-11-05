-- Prove2me | Theorems.Thm_CircuitLowerBound_Sched_bt_unary
-- name    : CircuitLowerBound.Sched.bt_unary
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T19:32:40.959347+00:00
-- url     : https://prove2.me/theorems/c8d89c70-4881-4ec5-bf47-0d1fe4d11298
-- title:
--   Sched: bt unary
-- statement:
--   The number of bits of a time is given in unary if L is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/Sched.lean#L137-L141
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/Sched.lean#L137-L141

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

theorem CircuitLowerBound.Sched.bt_unary {e : α → MCode} {L : α → ℕ} (he : PolyT e) (hL : Unary L) : Unary fun x => bt (e x) (L x) := by sorry
