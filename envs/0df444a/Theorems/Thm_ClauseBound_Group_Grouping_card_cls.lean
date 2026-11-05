-- Prove2me | Theorems.Thm_ClauseBound_Group_Grouping_card_cls
-- name    : ClauseBound.Group.Grouping.card_cls
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:45:47.068694+00:00
-- url     : https://prove2.me/theorems/564302ba-83f0-4bfc-b0a9-c6d8825d34e5
-- title:
--   Grouping: card cls
-- statement:
--   Every group has n nodes.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Group/Grouping.lean#L113-L122
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Group/Grouping.lean#L113-L122

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Group_Sample
import Definitions.Def_ClauseBound_Group_Grouping
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Group
open Finset
open ClauseBound.Group.Grouping
variable {K n : ℕ}

theorem ClauseBound.Group.Grouping.card_cls (e : Equiv.Perm (Fin (K * n))) (γ : Fin K) : #(cls e γ) = n := by sorry
