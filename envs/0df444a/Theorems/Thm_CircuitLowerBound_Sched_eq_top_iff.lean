-- Prove2me | Theorems.Thm_CircuitLowerBound_Sched_eq_top_iff
-- name    : CircuitLowerBound.Sched.eq_top_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:03:36.627667+00:00
-- url     : https://prove2.me/theorems/2ce9aace-baa5-4c0e-9c63-f7823755ee0a
-- title:
--   Sched: eq top iff
-- statement:
--   «s is the last place of chain a»: it is at most s and not at most s − 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/Sched.lean#L58-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/Sched.lean#L58-L61

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

theorem CircuitLowerBound.Sched.eq_top_iff (a s : ℕ) : s = top a ↔ (leTop a s && !leTop a (s - 1)) = true := by sorry
