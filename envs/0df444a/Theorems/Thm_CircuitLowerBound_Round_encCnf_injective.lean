-- Prove2me | Theorems.Thm_CircuitLowerBound_Round_encCnf_injective
-- name    : CircuitLowerBound.Round.encCnf_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:59:20.891237+00:00
-- url     : https://prove2.me/theorems/d90276b9-ee22-45d7-99c2-5b1417694c77
-- title:
--   Round: enc Cnf injective
-- statement:
--   The Round construction uses the enc Cnf injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Round.lean#L180-L198
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Round.lean#L180-L198

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

theorem CircuitLowerBound.Round.encCnf_injective {φ φ' : Cnf} (h : encCnf φ = encCnf φ') : φ = φ' := by sorry
