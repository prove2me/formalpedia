-- Prove2me | Theorems.Thm_CircuitLowerBound_Blocks_getD_toWord
-- name    : CircuitLowerBound.Blocks.getD_toWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:34:58.927952+00:00
-- url     : https://prove2.me/theorems/cbefc9c0-c042-4012-bee9-fbd5ac9ba3cb
-- title:
--   Blocks: get D to Word
-- statement:
--   The Blocks construction uses the get D to Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L280-L289
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L280-L289

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

theorem CircuitLowerBound.Blocks.getD_toWord {n j k : ℕ} (hk : k < n) : (toWord n j).getD k false = j.testBit k := by sorry
