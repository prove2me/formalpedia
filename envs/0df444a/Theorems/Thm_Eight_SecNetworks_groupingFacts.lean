-- Prove2me | Theorems.Thm_Eight_SecNetworks_groupingFacts
-- name    : Eight.SecNetworks.groupingFacts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:59:41.363856+00:00
-- url     : https://prove2.me/theorems/81351df3-13d1-4528-b048-39a6b423f9e2
-- title:
--   Sec Networks: grouping Facts
-- statement:
--   **«A good grouping exists»**: the steps of the paragraph at g = 3K⁸, with the numbers 4/(3K²),
--   2/3, K/g, 1/3 of the text. Same as in the paper, but for probabilities written as counts over the
--   K^g groupings.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Grouping.lean#L325-L357
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Grouping.lean#L325-L357

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_Defs
import Definitions.Def_Groundwork_Net_Colouring
import Definitions.Def_Groundwork_Net_Colouring
import Definitions.Def_Eight_SecNetworks_Grouping
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Eight Eight.SecNetworks
open Finset Groundwork.Colouring
variable {g K : ℕ}

theorem Eight.SecNetworks.groupingFacts : GroupingFacts := by sorry
