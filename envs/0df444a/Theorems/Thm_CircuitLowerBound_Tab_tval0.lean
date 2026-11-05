-- Prove2me | Theorems.Thm_CircuitLowerBound_Tab_tval0
-- name    : CircuitLowerBound.Tab.tval0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:36:53.670358+00:00
-- url     : https://prove2.me/theorems/2fb27bcc-2557-4252-af5d-e27b9371f4aa
-- title:
--   Tab: tval0
-- statement:
--   The Tab construction uses the tval0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Table.lean#L44-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Table.lean#L44-L44

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

theorem CircuitLowerBound.Tab.tval0 (b t : ℕ) : tval b t 0 = 0 := by sorry
