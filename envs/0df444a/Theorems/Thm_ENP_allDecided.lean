-- Prove2me | Theorems.Thm_ENP_allDecided
-- name    : ENP.allDecided
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:10:29.500512+00:00
-- url     : https://prove2.me/theorems/0d13e339-85b1-4602-9400-aaede5bd1909
-- title:
--   ENP: all Decided
-- statement:
--   Every set of words of length n is decided by some circuit.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Inf.lean#L122-L129
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Inf.lean#L122-L129

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
open CircuitLowerBound.Inf

theorem ENP.allDecided : ENP.AllDecided := by sorry
