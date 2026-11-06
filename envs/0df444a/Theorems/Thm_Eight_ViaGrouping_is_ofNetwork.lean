-- Prove2me | Theorems.Thm_Eight_ViaGrouping_is_ofNetwork
-- name    : Eight.ViaGrouping.is_ofNetwork
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:03:49.776066+00:00
-- url     : https://prove2.me/theorems/4cfd1e77-c372-437c-b208-a589de12dc0d
-- title:
--   Via Grouping: is of Network
-- statement:
--   Definition 2, all but (iii), with B + 1 for B: «at most 2^B» gives «below 2^{B+1}».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Bridge.lean#L58-L80
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Bridge.lean#L58-L80

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

theorem Eight.ViaGrouping.is_ofNetwork {C : Type} {Np : Paper.NetworkProcedures C} {c : C} {N : Paper.Network (Fin g) (List Bool) (List Bool)} {P B τ S : ℕ}
    (hP : 1 ≤ P) (h : Paper.IsNetwork Np c N P B τ S) : (ofNetwork N fun a => Np.n c a).Is P (B + 1) := by sorry
