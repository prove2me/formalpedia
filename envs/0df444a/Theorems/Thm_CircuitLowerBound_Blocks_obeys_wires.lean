-- Prove2me | Theorems.Thm_CircuitLowerBound_Blocks_obeys_wires
-- name    : CircuitLowerBound.Blocks.obeys_wires
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:34:53.042457+00:00
-- url     : https://prove2.me/theorems/610157fb-80b7-4d01-9264-cf794c29b5ef
-- title:
--   Blocks: obeys wires
-- statement:
--   The values of the wires of a circuit on an input obey the circuit.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L176-L190
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L176-L190

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Blocks
set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Blocks
open ENP Groundwork

theorem CircuitLowerBound.Blocks.obeys_wires (x : List Bool) (C : List GateD) (h : WFa x.length C) : Obeys (fun i => (wires x (toC C)).getD i false) x.length C := by sorry
