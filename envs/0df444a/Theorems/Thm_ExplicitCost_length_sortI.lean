-- Prove2me | Theorems.Thm_ExplicitCost_length_sortI
-- name    : ExplicitCost.length_sortI
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:11:31.416365+00:00
-- url     : https://prove2.me/theorems/5bb252f8-7289-4dd3-8757-b636e786a281
-- title:
--   Explicit Cost: length sort I
-- statement:
--   The list of 𝓘 has |𝓘| entries.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/GridLemmas.lean#L78-L78
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/GridLemmas.lean#L78-L78

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SquareGrid
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_GridLemmas
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.length_sortI (D : PiecesCounted.Data) (lam : ℕ) : ((D.fam lam).I.sort).length = #(D.fam lam).I := by sorry
