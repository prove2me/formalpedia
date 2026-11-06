-- Prove2me | Theorems.Thm_ExplicitCost_roomIsWithinTheBoundFrom
-- name    : ExplicitCost.roomIsWithinTheBoundFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:29:54.270827+00:00
-- url     : https://prove2.me/theorems/a02ad6d8-0ae7-45ba-bd83-8cb35aa0db33
-- title:
--   Explicit Cost: room Is Within The Bound From
-- statement:
--   `RoomIsWithinTheBoundFrom`, with C₀ = 2c + 3.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RoomWithin.lean#L68-L103
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RoomWithin.lean#L68-L103

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

theorem ExplicitCost.roomIsWithinTheBoundFrom : RoomIsWithinTheBoundFrom := by sorry
