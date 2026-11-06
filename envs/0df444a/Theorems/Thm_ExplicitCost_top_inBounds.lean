-- Prove2me | Theorems.Thm_ExplicitCost_top_inBounds
-- name    : ExplicitCost.top_inBounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:20:39.428873+00:00
-- url     : https://prove2.me/theorems/21016184-549b-4b3c-b8de-fa470420798d
-- title:
--   Explicit Cost: top in Bounds
-- statement:
--   The outermost instance is within the bounds that hold along the recursion from it.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/EndCounted.lean#L38-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/EndCounted.lean#L38-L41

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_EndBounds
import Definitions.Def_CountedRecursion_CliqueReads
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_EndCounted
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.top_inBounds (ρ : ℝ) (c x₀ l lam B : ℕ) : InBounds ρ c x₀ l lam B (top l lam B) := by sorry
