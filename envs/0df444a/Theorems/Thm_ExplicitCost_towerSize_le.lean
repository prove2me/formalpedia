-- Prove2me | Theorems.Thm_ExplicitCost_towerSize_le
-- name    : ExplicitCost.towerSize_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:22:49.650507+00:00
-- url     : https://prove2.me/theorems/f000bec7-0037-4bfa-97f1-56282e0eb415
-- title:
--   Explicit Cost: tower Size le
-- statement:
--   The bound for the tower from a bound for its parts: R ≤ mY with ℓ + 3 = m and Y ≥ 1 gives at
--   most 5m³Y.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/TotalRoom.lean#L27-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/TotalRoom.lean#L27-L37

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Chain
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_TotalRoom
set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed QueryMachines Finset

theorem ExplicitCost.towerSize_le {l R m Y : ℕ} (hm : m = l + 3) (hY : 1 ≤ Y) (hR : R ≤ m * Y) : Tower.towerSize l R R R ≤ 5 * (m ^ 3 * Y) := by sorry
