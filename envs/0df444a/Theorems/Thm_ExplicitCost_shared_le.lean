-- Prove2me | Theorems.Thm_ExplicitCost_shared_le
-- name    : ExplicitCost.shared_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:26:18.603204+00:00
-- url     : https://prove2.me/theorems/15729a18-946f-475a-9d4c-fda5f33fb479
-- title:
--   Explicit Cost: shared le
-- statement:
--   «and moreover c_{a,a'} ≤ g²λ».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CaseTwo.lean#L39-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CaseTwo.lean#L39-L43

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternPsi
import Definitions.Def_GeneralPieces_Rec_Chain
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CaseTwo
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.shared_le {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data} (hS : Setting ρ c x₀ D) (g : ℕ) {lam : ℕ} (hlam : 1 ≤ lam) (y : ℕ) (tr : Bool) (W : ℕ → List Bool → ℤ) (a b : Fin (nParts g g tr)) :
    (patternNet D c g tr lam y W).c a b ≤ g ^ 2 * lam := by sorry
