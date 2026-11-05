-- Prove2me | Theorems.Thm_CircuitLowerBound_Form_forall_append
-- name    : CircuitLowerBound.Form.forall_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:10:56.597673+00:00
-- url     : https://prove2.me/theorems/afa7f495-eb29-4f6c-9bb9-bd76f2687ee7
-- title:
--   Form: forall append
-- statement:
--   A statement on all gates of a list, with their numbers, for two lists one after the other.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L62-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L62-L79

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_ToTuring_Lib_Int
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Nat1b
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Form
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Form

theorem CircuitLowerBound.Form.forall_append (Q : ℕ → GateD → Prop) (N : ℕ) (A B : List GateD) :
    (∀ t (h : t < (A ++ B).length), Q (N + t) (A ++ B)[t]) ↔
      (∀ t (h : t < A.length), Q (N + t) A[t]) ∧ ∀ t (h : t < B.length), Q (N + A.length + t) B[t] := by sorry
