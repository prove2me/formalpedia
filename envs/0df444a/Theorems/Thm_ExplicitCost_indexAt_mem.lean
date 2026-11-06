-- Prove2me | Theorems.Thm_ExplicitCost_indexAt_mem
-- name    : ExplicitCost.indexAt_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:12:18.307871+00:00
-- url     : https://prove2.me/theorems/daea4a21-cd05-4eb1-add4-46a33e98f29a
-- title:
--   Explicit Cost: index At mem
-- statement:
--   The element number j < |𝓘| of 𝓘 is in 𝓘.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/GridLemmas.lean#L81-L85
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/GridLemmas.lean#L81-L85

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SquareGrid
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_GridLemmas
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.indexAt_mem (D : PiecesCounted.Data) (lam : ℕ) {j : ℕ} (hj : j < #(D.fam lam).I) : indexAt D lam j ∈ (D.fam lam).I := by sorry
