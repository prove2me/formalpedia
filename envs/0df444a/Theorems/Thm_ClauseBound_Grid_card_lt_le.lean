-- Prove2me | Theorems.Thm_ClauseBound_Grid_card_lt_le
-- name    : ClauseBound.Grid.card_lt_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:02:08.197027+00:00
-- url     : https://prove2.me/theorems/1f93ec39-2cae-4faf-9ee6-2c909b3b11e3
-- title:
--   Grid: card lt le
-- statement:
--   There are at most d² pairs of columns.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Size.lean#L68-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Size.lean#L68-L70

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_ClauseBound_Grid_Size
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Grid
open Finset Groundwork Groundwork.Grid

theorem ClauseBound.Grid.card_lt_le {d : ℕ} (X : Type) [Fintype X] [LinearOrder X] (hX : Fintype.card X = d) :
    #(univ.filter fun k : X × X => k.1 < k.2) ≤ d ^ 2 := by sorry
