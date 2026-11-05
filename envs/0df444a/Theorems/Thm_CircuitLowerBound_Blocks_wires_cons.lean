-- Prove2me | Theorems.Thm_CircuitLowerBound_Blocks_wires_cons
-- name    : CircuitLowerBound.Blocks.wires_cons
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T18:41:09.504889+00:00
-- url     : https://prove2.me/theorems/76afbcdb-c800-4264-bbaf-e4f9f31895fd
-- title:
--   Blocks: wires cons
-- statement:
--   The Blocks construction uses the wires cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L160-L160
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L160-L160

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

theorem CircuitLowerBound.Blocks.wires_cons (x : List Bool) (G : Gate) (C : Circuit) : wires x (G :: C) = wires (x ++ [G.op (x.getD G.in₁ false) (x.getD G.in₂ false)]) C := by sorry
