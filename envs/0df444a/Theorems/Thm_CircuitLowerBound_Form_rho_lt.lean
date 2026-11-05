-- Prove2me | Theorems.Thm_CircuitLowerBound_Form_rho_lt
-- name    : CircuitLowerBound.Form.rho_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:11:49.16371+00:00
-- url     : https://prove2.me/theorems/7372b818-b06d-4e16-8b59-dfabed5fb16d
-- title:
--   Form: rho lt
-- statement:
--   The Form construction uses the rho lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L236-L240
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L236-L240

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
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Form

theorem CircuitLowerBound.Form.rho_lt {L N : ℕ} {o : List ℕ} (ho : ∀ i, o.getD i 0 < N) (off : ℕ) {k t : ℕ} (hk : k < L + t) : rho L N o off k < N + t := by sorry
