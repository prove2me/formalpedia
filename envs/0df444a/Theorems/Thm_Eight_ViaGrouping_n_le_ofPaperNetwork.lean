-- Prove2me | Theorems.Thm_Eight_ViaGrouping_n_le_ofPaperNetwork
-- name    : Eight.ViaGrouping.n_le_ofPaperNetwork
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:04:33.349389+00:00
-- url     : https://prove2.me/theorems/acede0a3-d7be-4d77-b0eb-768a48b98405
-- title:
--   Via Grouping: n le of Paper Network
-- statement:
--   P_a ≤ P for a network of proof/networks/Paper: it has 2^{P_a} settings at a, and at most 2^P.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Bridge.lean#L51-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Bridge.lean#L51-L55

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Bridge
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Finset Stepped Eight.SecNetworks
variable {g : ℕ}

theorem Eight.ViaGrouping.n_le_ofPaperNetwork {C : Type} {Np : Paper.NetworkProcedures C} {c : C} {N : Paper.Network (Fin g) (List Bool) (List Bool)} {P B τ S : ℕ}
    (h : Paper.IsNetwork Np c N P B τ S) (a : Fin g) : Np.n c a ≤ P := by sorry
