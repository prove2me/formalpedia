-- Prove2me | Theorems.Thm_ExplicitCost_top_fits
-- name    : ExplicitCost.top_fits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:22:40.363671+00:00
-- url     : https://prove2.me/theorems/6c21cc27-0105-45ca-abd1-180ce4ff8f8b
-- title:
--   Explicit Cost: top fits
-- statement:
--   The outermost instance with its tables is «the (K_ℓ, λ)-clique with |W_w| < 2^B».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/EndCounted.lean#L44-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/EndCounted.lean#L44-L48

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_EndBounds
import Definitions.Def_CountedRecursion_CliqueReads
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_EndCounted
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.top_fits (x₀ l : ℕ) {lam B : ℕ} (hlam : 1 ≤ lam) (hB : 1 ≤ B) {W : ℕ → List Bool → ℤ} (hW : ∀ w < Levels.Gen.K x₀ l, ∀ z ∈ words ((Levels.Gen.K x₀ l - 1) * lam), |W w z| < 2 ^ B) :
    Fits x₀ (top l lam B) (answersOf (Levels.Gen.K x₀ l) lam W) := by sorry
