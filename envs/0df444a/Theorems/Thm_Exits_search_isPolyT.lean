-- Prove2me | Theorems.Thm_Exits_search_isPolyT
-- name    : Exits.search_isPolyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:32:17.396338+00:00
-- url     : https://prove2.me/theorems/a0568b1f-b1b5-4335-b3fb-f42519aa5ff7
-- title:
--   Exits: search is Poly T
-- statement:
--   The search of line 10, «try all groupings into K_ℓ groups until one is good», has
--   polynomial-time steps, if the loop that can be left early has.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Grouping.lean#L131-L139
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Grouping.lean#L131-L139

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_AlgDefs
import Definitions.Def_Eight_ViaGrouping_Main
import Definitions.Def_Eight_ViaGrouping_Keeps
import Definitions.Def_ToTuring_Poly_Range
import Mathlib.Tactic.GCongr
import Definitions.Def_Exits_Grouping
set_option autoImplicit false
section
section
open Exits
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Stepped Finset Paper Eight Eight.SecNetworks Eight.ViaGrouping Eight.ViaGrouping.Cost

theorem Exits.search_isPolyT (hF : StFoldUntilPoly) (K g : ℕ) {C : Type} [HasSize C] [Enc C] [Carried C] {Np : Procs C} (h : KeepsP Np) : Nonempty (IsPolyT (search K g Np)) := by sorry
