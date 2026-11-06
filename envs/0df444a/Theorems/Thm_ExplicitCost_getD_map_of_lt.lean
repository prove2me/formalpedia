-- Prove2me | Theorems.Thm_ExplicitCost_getD_map_of_lt
-- name    : ExplicitCost.getD_map_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:14:06.19386+00:00
-- url     : https://prove2.me/theorems/d99e24b8-7bfe-4bd9-a92b-d240b968506e
-- title:
--   Explicit Cost: get D map of lt
-- statement:
--   The element number j of a list under a map.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/GridLemmas.lean#L74-L75
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/GridLemmas.lean#L74-L75

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SquareGrid
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_GridLemmas
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.getD_map_of_lt {α β : Type} (f : α → β) (l : List α) {j : ℕ} (hj : j < l.length) (d : α) (d' : β) : (l.map f).getD j d' = f (l.getD j d) := by sorry
