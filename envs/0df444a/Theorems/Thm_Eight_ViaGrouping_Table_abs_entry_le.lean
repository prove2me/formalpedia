-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Table_abs_entry_le
-- name    : Eight.ViaGrouping.Table.abs_entry_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:09:42.137149+00:00
-- url     : https://prove2.me/theorems/3c7d6f5a-832e-42dc-a8ca-ac6bcc753fff
-- title:
--   Table: abs entry le
-- statement:
--   «… at most (2^P)^{2g/K} = 2^{2gP/K} terms, each a product of at most g² values. So |W̃_γ| <
--   2^{B'} with B' = ⌈2gP/K⌉ + g²B»: if every group has at most m nodes, an entry is at most 2^{Pm +
--   g²B} in absolute value.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L363-L377
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L363-L377

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

theorem Eight.ViaGrouping.Table.abs_entry_le (h : IsNetworkP Np c N P B τ S) (m : ℕ) (hm : ∀ G < K, (members K g x G).length ≤ m)
    (hβ : ∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g Np.toPaperNetwork c x G G' ≤ β) (hθ : ∀ G', G' ≠ G → (θ G').length = β) :
    |mergedVal K g Np.toPaperNetwork N.toPaperNetwork ((c, x), (G.val, List.ofFn θ))| ≤ 2 ^ (P * m + g ^ 2 * B) := by sorry
