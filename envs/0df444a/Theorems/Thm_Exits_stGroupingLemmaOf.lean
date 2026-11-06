-- Prove2me | Theorems.Thm_Exits_stGroupingLemmaOf
-- name    : Exits.stGroupingLemmaOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:33:19.854254+00:00
-- url     : https://prove2.me/theorems/b62fe4dc-71cc-4761-a919-26593b22c4ce
-- title:
--   Exits: st Grouping Lemma Of
-- statement:
--   **Lemma 1 for the algorithm of its proof**, with the search of line 10. «Let (K, e) be
--   achievable and g = 3K⁸. There is a constant C₁ = C₁(K, e) such that the value of every network on
--   [g] with parameters P, B, τ and total U is computed within C₁·2^{e(U + gP/K) + 2gP/K}·(P + B)^{C₁}·τ
--   operations.» From the run of the search and the three steps «a good grouping exists … fix the first
--   good one», «one entry costs …» and «so the value equals Z».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Grouping.lean#L124-L127
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Grouping.lean#L124-L127

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

theorem Exits.stGroupingLemmaOf : StGroupingLemmaOf := by sorry
