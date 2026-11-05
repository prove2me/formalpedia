-- Prove2me | Theorems.Thm_ClauseBound_Rec_pow_mul_sum_choose_le
-- name    : ClauseBound.Rec.pow_mul_sum_choose_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:24:29.464704+00:00
-- url     : https://prove2.me/theorems/9b96a91b-fd32-43c8-b227-cd67c16de5aa
-- title:
--   Rec: pow mul sum choose le
-- statement:
--   For 0 ≤ y ≤ 1: y^n·Σ_{ν≤n} C(δ, ν) ≤ (1 + y)^δ, provided n ≤ δ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/Few.lean#L35-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/Few.lean#L35-L43

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic
import Definitions.Def_ClauseBound_Rec_Few
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Rec
open Finset

theorem ClauseBound.Rec.pow_mul_sum_choose_le {δ n : ℕ} (h2 : n ≤ δ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    y ^ n * ∑ ν ∈ range (n + 1), (δ.choose ν : ℝ) ≤ (y + 1) ^ δ := by sorry
