-- Prove2me | Theorems.Thm_CircuitLowerBound_Tab_mem_en
-- name    : CircuitLowerBound.Tab.mem_en
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:43:22.6512+00:00
-- url     : https://prove2.me/theorems/0481c61b-d283-4b22-a487-572be2f528a8
-- title:
--   Tab: mem en
-- statement:
--   The Tab construction uses the mem en property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Table.lean#L60-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Table.lean#L60-L60

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

theorem CircuitLowerBound.Tab.mem_en {ι : Type} [Finite ι] (i : ι) : i ∈ en ι := by sorry
