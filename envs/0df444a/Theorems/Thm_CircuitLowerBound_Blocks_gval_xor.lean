-- Prove2me | Theorems.Thm_CircuitLowerBound_Blocks_gval_xor
-- name    : CircuitLowerBound.Blocks.gval_xor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:14:51.31994+00:00
-- url     : https://prove2.me/theorems/9ad43e0a-7326-430a-927b-f76477fe4052
-- title:
--   Blocks: gval xor
-- statement:
--   The Blocks construction uses the gval xor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L62-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L62-L63

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

theorem CircuitLowerBound.Blocks.gval_xor (v : ℕ → Bool) (i j : ℕ) : gval v (opXor, i, j) = (v i ^^ v j) := by sorry
