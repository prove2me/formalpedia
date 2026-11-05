-- Prove2me | Theorems.Thm_CircuitLowerBound_Tab_length_nxt_le
-- name    : CircuitLowerBound.Tab.length_nxt_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:28:35.270377+00:00
-- url     : https://prove2.me/theorems/0ad9964f-76ee-4597-9bbf-fe0a392390a4
-- title:
--   Tab: length nxt le
-- statement:
--   The new top of a stack has at most 2d symbols.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Frame.lean#L195-L204
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Frame.lean#L195-L204

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Spec
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Frame
set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Tab
open ENP Turing
variable (N : TM2ComputableAux Bool Bool)

theorem CircuitLowerBound.Tab.length_nxt_le (γ : Case N) (k : N.tm.K) : ((nxt N γ).stk k).length ≤ 2 * dep N := by sorry
