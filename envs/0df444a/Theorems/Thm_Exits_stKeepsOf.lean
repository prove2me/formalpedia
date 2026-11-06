-- Prove2me | Theorems.Thm_Exits_stKeepsOf
-- name    : Exits.stKeepsOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:33:41.754607+00:00
-- url     : https://prove2.me/theorems/f810d231-41ac-43f8-b853-e493a17f6780
-- title:
--   Exits: st Keeps Of
-- statement:
--   **The algorithm of the proof of Lemma 1, with the search of line 10, has polynomial-time steps**
--   if the algorithm E for cliques has. A bound on the number of steps («… is computed within C₁·2^{e(U +
--   gP/K) + 2gP/K}·(P + B)^{C₁}·τ operations») bounds the time only if each step takes polynomial time;
--   this is that half. From the polynomial-time steps of the loop.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Grouping.lean#L145-L154
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Grouping.lean#L145-L154

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

theorem Exits.stKeepsOf : StKeepsOf := by sorry
