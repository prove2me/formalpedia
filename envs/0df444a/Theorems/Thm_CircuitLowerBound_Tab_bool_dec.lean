-- Prove2me | Theorems.Thm_CircuitLowerBound_Tab_bool_dec
-- name    : CircuitLowerBound.Tab.bool_dec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:39:26.124354+00:00
-- url     : https://prove2.me/theorems/2724cce7-51c2-433a-97d9-27856de6201f
-- title:
--   Tab: bool dec
-- statement:
--   The Tab construction uses the bool dec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Table.lean#L117-L118
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Table.lean#L117-L118

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Frame
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Table
set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Tab
open ENP Turing
variable (N : TM2ComputableAux Bool Bool)
variable {N}
variable (N) [Finite (Case N)] [∀ k, Finite (N.tm.Γ k)]
variable {N}

theorem CircuitLowerBound.Tab.bool_dec {y : Bool} {p : Prop} [Decidable p] : y = decide p ↔ (y = true ↔ p) := by sorry
