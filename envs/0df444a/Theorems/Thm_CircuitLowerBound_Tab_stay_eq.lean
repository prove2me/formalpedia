-- Prove2me | Theorems.Thm_CircuitLowerBound_Tab_stay_eq
-- name    : CircuitLowerBound.Tab.stay_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:28:43.875075+00:00
-- url     : https://prove2.me/theorems/fcb4d045-0d29-473f-8cd3-9db7702696a7
-- title:
--   Tab: stay eq
-- statement:
--   The step, written with the case of the configuration.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Frame.lean#L178-L192
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Frame.lean#L178-L192

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

theorem CircuitLowerBound.Tab.stay_eq (c : N.tm.Cfg) : stay N c =
    ⟨(nxt N (caseOf N c)).l, (nxt N (caseOf N c)).var, fun k => (nxt N (caseOf N c)).stk k ++ (c.stk k).drop (dep N)⟩ := by sorry
