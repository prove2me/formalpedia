-- Prove2me | Theorems.Thm_ExplicitCost_own_le
-- name    : ExplicitCost.own_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:29:57.302328+00:00
-- url     : https://prove2.me/theorems/4d56adaa-e7cd-4d08-9031-73ae1c6a3d4d
-- title:
--   Explicit Cost: own le
-- statement:
--   The same with the powers of Ξ. X = Ξ, s = 2^{2N/K}, u = 2^{cΛ}, a the number of functions ι : ℛ
--   → 𝓘, κ = K^g, T the bound for the level below (the premise `BoundBelow`), t the price of a query to
--   the tables.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CountStep.lean#L60-L67
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CountStep.lean#L60-L67

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

theorem ExplicitCost.own_le {X T s u a κ q t : ℝ} (C : ℕ) (hX : 2 ≤ X) (hT : 1 ≤ T) (hs : 1 ≤ s) (hu : 1 ≤ u) (ht : 1 ≤ t) (ha : 0 ≤ a) :
    a * (X ^ C * κ) + q + X ^ C + a * ((s * X ^ C * (u + 2) + s * X ^ C * t + 2) * T + 2) ≤
      a * ((κ + t * T * s * (u * X ^ (C + 3))) * X ^ C + 2 * X ^ C) + q + X ^ C := by sorry
