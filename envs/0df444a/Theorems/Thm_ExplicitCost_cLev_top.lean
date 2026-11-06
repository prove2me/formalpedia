-- Prove2me | Theorems.Thm_ExplicitCost_cLev_top
-- name    : ExplicitCost.cLev_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:21:48.887194+00:00
-- url     : https://prove2.me/theorems/ac180ee1-2eff-4618-9b41-019ef30dae3f
-- title:
--   Explicit Cost: c Lev top
-- statement:
--   The level of the outermost instance.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/EndCounted.lean#L29-L29
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/EndCounted.lean#L29-L29

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

theorem ExplicitCost.cLev_top (l lam B : ℕ) : cLev (top l lam B) = l := by sorry
