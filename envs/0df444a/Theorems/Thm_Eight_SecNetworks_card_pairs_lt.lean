-- Prove2me | Theorems.Thm_Eight_SecNetworks_card_pairs_lt
-- name    : Eight.SecNetworks.card_pairs_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:11:40.905713+00:00
-- url     : https://prove2.me/theorems/da53447e-0b54-40a9-92e3-9a8a23caca95
-- title:
--   Sec Networks: card pairs lt
-- statement:
--   «the fewer than K²/2 pairs of groups»: there are K(K − 1)/2 pairs γ < γ'.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Grouping.lean#L203-L231
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Grouping.lean#L203-L231

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

theorem Eight.SecNetworks.card_pairs_lt (hK : 1 ≤ K) : 2 * #{p : Fin K × Fin K | p.1 < p.2} < K ^ 2 := by sorry
