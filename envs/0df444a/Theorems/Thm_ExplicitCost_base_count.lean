-- Prove2me | Theorems.Thm_ExplicitCost_base_count
-- name    : ExplicitCost.base_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:26:08.573198+00:00
-- url     : https://prove2.me/theorems/98087e99-a060-4d19-aa03-0ff5a6887b3f
-- title:
--   Explicit Cost: base count
-- statement:
--   The arithmetic on natural numbers: A(k + 1) + Akt ≤ t·(A·X^n) for 1 ≤ k, 2k ≤ X, n ≥ 2, t ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CountBase.lean#L28-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CountBase.lean#L28-L40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_LevelBound
import Definitions.Def_GeneralPieces_Rec_Rate
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CountBase
set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed

theorem ExplicitCost.base_count {A k X n t : ℕ} (hk : 1 ≤ k) (hX : 2 * k ≤ X) (hn : 2 ≤ n) (ht : 1 ≤ t) : A * (k + 1) + 0 * 0 + A * k * t ≤ t * (A * X ^ n) := by sorry
