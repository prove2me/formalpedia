-- Prove2me | Theorems.Thm_Eight_ViaGrouping_lamP_polyT
-- name    : Eight.ViaGrouping.lamP_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:35:34.619313+00:00
-- url     : https://prove2.me/theorems/9b7612ab-5602-4c57-8013-2620f7239886
-- title:
--   Via Grouping: lam P poly T
-- statement:
--   L is computable in polynomial time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Keeps.lean#L39-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Keeps.lean#L39-L43

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_ToTuring_Poly_Basic
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_Eight_ViaGrouping_Keeps
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Stepped Eight.SecNetworks
variable {C : Type} [HasSize C] [Enc C] [Carried C] (K g : ℕ) {Np : Procs C}

theorem Eight.ViaGrouping.lamP_polyT (h : KeepsP Np) : PolyT (lamP K g Np) := by sorry
