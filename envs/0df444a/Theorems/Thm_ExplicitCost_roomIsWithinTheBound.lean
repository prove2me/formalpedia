-- Prove2me | Theorems.Thm_ExplicitCost_roomIsWithinTheBound
-- name    : ExplicitCost.roomIsWithinTheBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:29:44.550411+00:00
-- url     : https://prove2.me/theorems/41c6c8ee-c650-450d-9ee7-1fa01121a7ba
-- title:
--   Explicit Cost: room Is Within The Bound
-- statement:
--   `RoomIsWithinTheBound`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RoomWithin.lean#L106-L106
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RoomWithin.lean#L106-L106

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_LevelBound
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_RoomWithin
set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed Finset

theorem ExplicitCost.roomIsWithinTheBound : RoomIsWithinTheBound := by sorry
