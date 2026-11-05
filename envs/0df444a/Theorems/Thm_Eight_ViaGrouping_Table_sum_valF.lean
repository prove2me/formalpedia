-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Table_sum_valF
-- name    : Eight.ViaGrouping.Table.sum_valF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:09:47.724523+00:00
-- url     : https://prove2.me/theorems/30c3eed0-ed62-4257-b518-3599eef2912e
-- title:
--   Table: sum val F
-- statement:
--   The sum over the 2^{c_{a,b}} strings θ by which `termVal` is defined inside a group is the
--   Ψ_{a,b} of `N.toPaperNetwork`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L203-L209
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L203-L209

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Table
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Table
variable {C : Type} [HasSize C] {K g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
variable {x β : ℕ} {G : Fin K} {θ : Fin K → List Bool}

theorem Eight.ViaGrouping.Table.sum_valF (h : N.Is P B) {a b : ℕ} (ha : a < g) (hb : b < g) (z z' : List Bool) :
    ∑ y ∈ range (2 ^ N.c ⟨a, ha⟩ ⟨b, hb⟩), valF N.toPaperNetwork a b z (toWord (N.c ⟨a, ha⟩ ⟨b, hb⟩) y) * valF N.toPaperNetwork b a z' (toWord (N.c ⟨a, ha⟩ ⟨b, hb⟩) y) =
      N.toPaperNetwork.Ψ ⟨a, ha⟩ ⟨b, hb⟩ z z' := by sorry
