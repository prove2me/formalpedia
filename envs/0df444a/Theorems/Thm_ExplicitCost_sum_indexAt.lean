-- Prove2me | Theorems.Thm_ExplicitCost_sum_indexAt
-- name    : ExplicitCost.sum_indexAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:14:56.874202+00:00
-- url     : https://prove2.me/theorems/12b23eea-33be-463c-82c6-245aae01e742
-- title:
--   Explicit Cost: sum index At
-- statement:
--   A sum over 𝓘 is the sum over its places.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/GridLemmas.lean#L111-L114
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/GridLemmas.lean#L111-L114

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

theorem ExplicitCost.sum_indexAt (D : PiecesCounted.Data) (lam : ℕ) (f : ℤ → ℤ) : ∑ j ∈ range #(D.fam lam).I, f (indexAt D lam j) = ∑ i ∈ (D.fam lam).I, f i := by sorry
