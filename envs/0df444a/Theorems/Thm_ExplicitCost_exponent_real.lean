-- Prove2me | Theorems.Thm_ExplicitCost_exponent_real
-- name    : ExplicitCost.exponent_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:18:00.153197+00:00
-- url     : https://prove2.me/theorems/4199ebbe-e047-452d-8815-ce6019400831
-- title:
--   Explicit Cost: exponent real
-- statement:
--   The arithmetic of `ChainExponent`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Chain.lean#L41-L49
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Chain.lean#L41-L49

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_ChainLabel
import Definitions.Def_CountedRecursion_CrudeBounds
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_CountedRecursion_PartAPrinted
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Chain
set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed

theorem ExplicitCost.exponent_real {e0 r G4 Λ cc lg k2 kk x : ℝ} (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) (hkk : 0 < kk) (hcl : 0 ≤ cc / 4 * G4 * lg) (hk2 : 0 ≤ k2) (h : x ≤ r * (G4 * Λ) + cc / 4 * G4 * lg + k2) :
    e0 * x + 3 * (G4 * Λ) / kk ≤ (r * e0 + 3 / kk) * G4 * Λ + cc / 4 * G4 * lg + k2 := by sorry
