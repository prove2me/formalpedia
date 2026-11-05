-- Prove2me | Theorems.Thm_CircuitLowerBound_Tab_num_injective
-- name    : CircuitLowerBound.Tab.num_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:43:19.805237+00:00
-- url     : https://prove2.me/theorems/310cafbc-bdb0-4b53-8196-fb9636e27c44
-- title:
--   Tab: num injective
-- statement:
--   The Tab construction uses the num injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Table.lean#L249-L250
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Table.lean#L249-L250

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

theorem CircuitLowerBound.Tab.num_injective : Function.Injective (num (N := N)) := by sorry
