-- Prove2me | Theorems.Thm_CircuitLowerBound_Form_wires_cons
-- name    : CircuitLowerBound.Form.wires_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:11:03.73796+00:00
-- url     : https://prove2.me/theorems/7ae5f01c-60c5-4e05-b97a-7c0a3b08842a
-- title:
--   Form: wires cons
-- statement:
--   The Form construction uses the wires cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L43-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L43-L44

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

theorem CircuitLowerBound.Form.wires_cons (w : List Bool) (G : Gate) (C : Circuit) :
    wires w (G :: C) = wires (w ++ [G.op (w.getD G.in₁ false) (w.getD G.in₂ false)]) C := by sorry
