-- Prove2me | Theorems.Thm_ExplicitCost_room_le
-- name    : ExplicitCost.room_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:21:24.906674+00:00
-- url     : https://prove2.me/theorems/fc3f5887-fbe4-44c7-a55d-370bfa86f595
-- title:
--   Explicit Cost: room le
-- statement:
--   The sizes of the states of the four procedures are at most Ξ^{C₂}. Here sp is the size of the
--   parent, sQ that of the query.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/BothNetworks.lean#L66-L88
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/BothNetworks.lean#L66-L88

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RowFactorRun
import Definitions.Def_CountedRecursion_ParentSize
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_BothNetworks
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.room_le {c g lam B sp sQ S : ℕ} (hg : 2 ≤ g) (hlam : 1 ≤ lam) (hB : 1 ≤ B) (hsp : sp ≤ Xi g lam B ^ (2 * c + 4)) (hsq : sQ ≤ 2 * (g + 2) + 2 * (2 * (g * (g * g) * lam) + 1))
    (hS : S ≤ 2 * (sp + sQ) + 2 * (g * g + 2) + (2 * lam) ^ c * (g * g) + (2 * lam) ^ c + B * g + B + 12) : S ≤ Xi g lam B ^ (2 * c + 6) := by sorry
