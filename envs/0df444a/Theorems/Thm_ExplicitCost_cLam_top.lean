-- Prove2me | Theorems.Thm_ExplicitCost_cLam_top
-- name    : ExplicitCost.cLam_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:19:05.946755+00:00
-- url     : https://prove2.me/theorems/f32a5c21-9785-4b14-9b20-5a9d67b1414e
-- title:
--   Explicit Cost: c Lam top
-- statement:
--   Its label length.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/EndCounted.lean#L32-L32
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/EndCounted.lean#L32-L32

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

theorem ExplicitCost.cLam_top (l lam B : ℕ) : cLam (top l lam B) = lam := by sorry
