-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Table_size_query_le
-- name    : Eight.ViaGrouping.Table.size_query_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:09:34.48719+00:00
-- url     : https://prove2.me/theorems/46adb352-8924-478c-998a-874d24d68d6b
-- title:
--   Table: size query le
-- statement:
--   The size of a well-formed query.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L154-L171
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L154-L171

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Table
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Table
variable {C : Type} [HasSize C] {K g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
variable {x β : ℕ} {G : Fin K} {θ : Fin K → List Bool}

theorem Eight.ViaGrouping.Table.size_query_le (hθ : ∀ G', G' ≠ G → (θ G').length = β) (hG : θ G = []) :
    size ((c, x), (G.val, List.ofFn θ)) ≤ size c + size x + size K + K * (2 * β + 2) + 1 := by sorry
