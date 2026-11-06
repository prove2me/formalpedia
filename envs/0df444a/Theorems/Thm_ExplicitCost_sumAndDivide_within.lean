-- Prove2me | Theorems.Thm_ExplicitCost_sumAndDivide_within
-- name    : ExplicitCost.sumAndDivide_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:07:57.869716+00:00
-- url     : https://prove2.me/theorems/1b2e8d84-84a6-47bc-8f35-c103001f4f3a
-- title:
--   Explicit Cost: sum And Divide within
-- statement:
--   «adding one Z_ι», for all ι; then «computing d^{|ℛ|} and dividing by it»: if the pattern number
--   y costs T₀ and has the value v y, |v y| ≤ V, the whole costs |𝓘|^{|ℛ|}·(T₀ + 1) + 2 operations.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverStages.lean#L124-L136
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverStages.lean#L124-L136

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverDefs
import Definitions.Def_CountedRecursion_Within
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverStages
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork QueryMachines Printed
variable {Q α : Type}

theorem ExplicitCost.sumAndDivide_within {c : ℕ} {O : SolQuery → Option Ans} {w : SolQuery → ℕ} {r : Ready} (T₀ Sm V : ℕ) (v : ℕ → ℤ) (hM : ∀ y < nPatterns r, (patternValue c).Within O w (r, y) T₀ Sm (v y))
    (hV : ∀ y < nPatterns r, (v y).natAbs ≤ V) :
    (sumAndDivide c).Within O w r (nPatterns r * (T₀ + 1) + 2) (2 * size r + size (nPatterns r) + size (nPatterns r * V) + Sm + 3) ((∑ y ∈ range (nPatterns r), v y) / (((rD r).toNat ^ rRect r : ℕ) : ℤ)) := by sorry
