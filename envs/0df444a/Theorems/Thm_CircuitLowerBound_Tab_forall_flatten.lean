-- Prove2me | Theorems.Thm_CircuitLowerBound_Tab_forall_flatten
-- name    : CircuitLowerBound.Tab.forall_flatten
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:31:50.186531+00:00
-- url     : https://prove2.me/theorems/88efc7dd-8740-4cb4-8da7-d75564740894
-- title:
--   Tab: forall flatten
-- statement:
--   The Tab construction uses the forall flatten property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Table.lean#L68-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Table.lean#L68-L70

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

theorem CircuitLowerBound.Tab.forall_flatten {β : Type} {p : β → Prop} {Ls : List (List β)} : (∀ c ∈ Ls.flatten, p c) ↔ ∀ l ∈ Ls, ∀ c ∈ l, p c := by sorry
