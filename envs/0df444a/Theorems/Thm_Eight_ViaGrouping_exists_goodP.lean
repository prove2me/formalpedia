-- Prove2me | Theorems.Thm_Eight_ViaGrouping_exists_goodP
-- name    : Eight.ViaGrouping.exists_goodP
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:01:25.292195+00:00
-- url     : https://prove2.me/theorems/4a8d01bf-fb11-4f7a-a316-f20d30432f54
-- title:
--   Via Grouping: exists good P
-- statement:
--   For g = 3K⁸ the test says yes to some number below K^g: «a good grouping exists»
--   (`SecNetworks.groupingFacts`), from c_{a,b} = c_{b,a} and (i) of Definition 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Search.lean#L93-L97
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Search.lean#L93-L97

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Definitions.Def_Eight_SecNetworks_Grouping
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Search
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
variable {C : Type} [HasSize C] {Np : Procs C} {c : C} {g K : ℕ} {N : Net g} {P B τ S : ℕ}

theorem Eight.ViaGrouping.exists_goodP (hK : 2 ≤ K) {N : Net (3 * K ^ 8)} (h : IsNetworkP Np c N P B τ S) : ∃ x < K ^ (3 * K ^ 8), goodP K (3 * K ^ 8) Np (c, x) = true := by sorry
