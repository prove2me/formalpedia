-- Prove2me | Theorems.Thm_ExplicitCost_cB_top
-- name    : ExplicitCost.cB_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:22:10.541941+00:00
-- url     : https://prove2.me/theorems/8d44f9d4-3204-4377-8218-8093ad29829b
-- title:
--   Explicit Cost: c B top
-- statement:
--   Its bound on the bits of the tables.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/EndCounted.lean#L35-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/EndCounted.lean#L35-L35

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

theorem ExplicitCost.cB_top (l lam B : ℕ) : cB (top l lam B) = B := by sorry
