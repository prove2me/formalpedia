-- Prove2me | Theorems.Thm_CircuitLowerBound_Blocks_wires_input
-- name    : CircuitLowerBound.Blocks.wires_input
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T18:34:13.577003+00:00
-- url     : https://prove2.me/theorems/494cbaab-46ca-4359-8cd9-209ccc8d65d3
-- title:
--   Blocks: wires input
-- statement:
--   The input wires carry the input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L172-L173
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L172-L173

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

theorem CircuitLowerBound.Blocks.wires_input (x : List Bool) (C : Circuit) {i : ℕ} (hi : i < x.length) : (wires x C).getD i false = x.getD i false := by sorry
