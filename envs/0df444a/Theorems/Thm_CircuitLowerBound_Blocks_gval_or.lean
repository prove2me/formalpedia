-- Prove2me | Theorems.Thm_CircuitLowerBound_Blocks_gval_or
-- name    : CircuitLowerBound.Blocks.gval_or
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:14:51.155974+00:00
-- url     : https://prove2.me/theorems/43572c44-d1b8-4e89-939a-b75ac4a14d89
-- title:
--   Blocks: gval or
-- statement:
--   The Blocks construction uses the gval or property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L59-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L59-L60

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

theorem CircuitLowerBound.Blocks.gval_or (v : ℕ → Bool) (i j : ℕ) : gval v (opOr, i, j) = (v i || v j) := by sorry
