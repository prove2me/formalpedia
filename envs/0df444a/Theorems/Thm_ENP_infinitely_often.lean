-- Prove2me | Theorems.Thm_ENP_infinitely_often
-- name    : ENP.infinitely_often
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:10:38.402461+00:00
-- url     : https://prove2.me/theorems/7cf9a443-fe80-4d58-b4c5-966e1846b364
-- title:
--   ENP: infinitely often
-- statement:
--   A language that is not decided by circuits of linear size fails at infinitely many lengths, for
--   every c.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Inf.lean#L133-L148
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Inf.lean#L133-L148

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

theorem ENP.infinitely_often {L : ENP.Lang} (h : ¬ENP.HasLinearCircuits L) (c N : ℕ) : ∃ n, N ≤ n ∧ ¬ENP.DecidedAt L (c * (n + 1)) n := by sorry
