-- Prove2me | Theorems.Thm_CircuitLowerBound_stTab_of
-- name    : CircuitLowerBound.stTab_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:43:29.791959+00:00
-- url     : https://prove2.me/theorems/dfcc9b53-4a06-4ff1-9f46-dd193a22058c
-- title:
--   Circuit Lower Bound: st Tab of
-- statement:
--   Every machine has a table.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Glue.lean#L20-L26
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Glue.lean#L20-L26

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Spec
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Glue
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Turing Tab

theorem CircuitLowerBound.stTab_of (h1 : StPack) (h2 : StSpec) (h3 : StSpecTab) : StTab := by sorry
