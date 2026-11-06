-- Prove2me | Theorems.Thm_CircuitLowerBound_Norm_toGate_op
-- name    : CircuitLowerBound.Norm.toGate_op
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:43:38.568263+00:00
-- url     : https://prove2.me/theorems/f1b484dd-06f4-4c04-88ba-8ca8e5b95a94
-- title:
--   Norm: to Gate op
-- statement:
--   The Norm construction uses the to Gate op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Norm.lean#L39-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Norm.lean#L39-L40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Norm
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Norm

theorem CircuitLowerBound.Norm.toGate_op (n : ℕ) (G : Gate) (x y : Bool) : (ng n G).toGate.op x y = op' n G x y := by sorry
