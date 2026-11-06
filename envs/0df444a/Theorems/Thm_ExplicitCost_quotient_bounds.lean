-- Prove2me | Theorems.Thm_ExplicitCost_quotient_bounds
-- name    : ExplicitCost.quotient_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:16:12.189128+00:00
-- url     : https://prove2.me/theorems/525b2a21-4bec-4478-af53-0e5797c25bcc
-- title:
--   Explicit Cost: quotient bounds
-- statement:
--   The number whose floor is Λ_j lies between 1 and g⁴Λ + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ChainLabel.lean#L64-L78
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ChainLabel.lean#L64-L78

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_LevelNumbers
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_ChainLabel
set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}

theorem ExplicitCost.quotient_bounds {r G4 Λ lg cc k2 : ℝ} (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hG : 0 ≤ G4) (hΛ : 0 ≤ Λ) (hlg0 : 0 ≤ lg) (hlg : lg ≤ Λ) (hc0 : 0 ≤ cc) (hk : 2 + cc / 4 ≤ k2) :
    1 ≤ (r * (G4 * Λ) + cc / 4 * G4 * lg + k2) / k2 ∧ (r * (G4 * Λ) + cc / 4 * G4 * lg + k2) / k2 ≤ G4 * Λ + 1 := by sorry
