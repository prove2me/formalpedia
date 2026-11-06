-- Prove2me | Theorems.Thm_CircuitLowerBound_Inf_ext_proj
-- name    : CircuitLowerBound.Inf.ext_proj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:10:24.530265+00:00
-- url     : https://prove2.me/theorems/49e06692-6a41-498a-90ee-ce0dbb3c7926
-- title:
--   Inf: ext proj
-- statement:
--   The Inf construction uses the ext proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Inf.lean#L80-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Inf.lean#L80-L81

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBoundInfinitelyOftenStatement
import Definitions.Def_CircuitLowerBound_Closed
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Inf
set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Inf
open ENP

theorem CircuitLowerBound.Inf.ext_proj {n i : ℕ} (hi : i < n) : Ext n fun x => x.getD i false := by sorry
