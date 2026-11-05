-- Prove2me | Theorems.Thm_CircuitLowerBound_Blocks_gval_fst
-- name    : CircuitLowerBound.Blocks.gval_fst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:34:10.671744+00:00
-- url     : https://prove2.me/theorems/18c38328-2c3d-4b15-9efc-5c5f7306aed9
-- title:
--   Blocks: gval fst
-- statement:
--   The Blocks construction uses the gval fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L65-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L65-L66

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

theorem CircuitLowerBound.Blocks.gval_fst (v : ℕ → Bool) (i j : ℕ) : gval v (opFst, i, j) = v i := by sorry
