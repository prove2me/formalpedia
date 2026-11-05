-- Prove2me | Theorems.Thm_CircuitLowerBound_Norm_value_ng
-- name    : CircuitLowerBound.Norm.value_ng
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T18:43:43.621521+00:00
-- url     : https://prove2.me/theorems/1c442063-7338-4ce5-a0b0-9b17bd74bb73
-- title:
--   Norm: value ng
-- statement:
--   The gate `ng w.length G` has the value of G.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Norm.lean#L48-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Norm.lean#L48-L55

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

theorem CircuitLowerBound.Norm.value_ng (w : List Bool) (G : Gate) :
    (ng w.length G).toGate.op (w.getD (ng w.length G).toGate.in₁ false) (w.getD (ng w.length G).toGate.in₂ false)
      = G.op (w.getD G.in₁ false) (w.getD G.in₂ false) := by sorry
