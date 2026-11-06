-- Prove2me | Theorems.Thm_ExplicitCost_size_list_bound
-- name    : ExplicitCost.size_list_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:26:07.140827+00:00
-- url     : https://prove2.me/theorems/a9df79fc-ea88-4c42-9ade-9f0b3fcd1304
-- title:
--   Explicit Cost: size list bound
-- statement:
--   The size of a list of at most k elements of size at most s.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ParentSize.lean#L27-L33
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ParentSize.lean#L27-L33

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CallParts
import Definitions.Def_ClauseBound_Gen_RateAux
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_ParentSize
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.size_list_bound {α : Type} [HasSize α] {l : List α} {k s : ℕ} (hl : l.length ≤ k) (hs : ∀ x ∈ l, size x ≤ s) : size l ≤ k * (s + 1) + 1 := by sorry
