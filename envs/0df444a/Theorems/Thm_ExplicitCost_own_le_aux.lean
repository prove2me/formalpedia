-- Prove2me | Theorems.Thm_ExplicitCost_own_le_aux
-- name    : ExplicitCost.own_le_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:28:31.004998+00:00
-- url     : https://prove2.me/theorems/d5b87a35-0d9b-495f-addd-bf4e2f2f2414
-- title:
--   Explicit Cost: own le aux
-- statement:
--   The costs of one level, in real variables, in the form of the printed sum; Y stands for Ξ^C and
--   Z for Ξ³.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CountStep.lean#L32-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CountStep.lean#L32-L55

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_LevelBound
import Definitions.Def_GeneralPieces_Rec_Count
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CountStep
set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed QueryMachines

theorem ExplicitCost.own_le_aux {Y Z T s u a κ q t : ℝ} (hY : 1 ≤ Y) (hZ : 8 ≤ Z) (hT : 1 ≤ T) (hs : 1 ≤ s) (hu : 1 ≤ u) (ht : 1 ≤ t) (ha : 0 ≤ a) :
    a * (Y * κ) + q + Y + a * ((s * Y * (u + 2) + s * Y * t + 2) * T + 2) ≤ a * ((κ + t * T * s * (u * (Y * Z))) * Y + 2 * Y) + q + Y := by sorry
