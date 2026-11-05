-- Prove2me | Theorems.Thm_CircuitLowerBound_Norm_wires_norm
-- name    : CircuitLowerBound.Norm.wires_norm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T18:43:44.727952+00:00
-- url     : https://prove2.me/theorems/24e2a07e-c376-4121-84bf-0cc37fcad959
-- title:
--   Norm: wires norm
-- statement:
--   All wires keep their values.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Norm.lean#L58-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Norm.lean#L58-L66

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

theorem CircuitLowerBound.Norm.wires_norm (C : Circuit) (w : List Bool) : wires w (toC (norm w.length C)) = wires w C := by sorry
