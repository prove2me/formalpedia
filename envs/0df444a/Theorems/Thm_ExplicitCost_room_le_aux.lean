-- Prove2me | Theorems.Thm_ExplicitCost_room_le_aux
-- name    : ExplicitCost.room_le_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:28:50.094568+00:00
-- url     : https://prove2.me/theorems/ac3ec76d-4700-4f28-b28e-3ca6819ab0ce
-- title:
--   Explicit Cost: room le aux
-- statement:
--   (u + P + 8)(P + 8) ≤ u·X^{2c+3}, for P ≤ X^c, 8 ≤ X, c ≥ 1, u ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RoomWithin.lean#L27-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RoomWithin.lean#L27-L41

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

theorem ExplicitCost.room_le_aux {u P X c : ℕ} (hP : P ≤ X ^ c) (hX : 8 ≤ X) (hc : 1 ≤ c) (hu : 1 ≤ u) : (u + P + 8) * (P + 8) ≤ u * X ^ (2 * c + 3) := by sorry
