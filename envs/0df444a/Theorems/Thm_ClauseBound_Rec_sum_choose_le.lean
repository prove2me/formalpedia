-- Prove2me | Theorems.Thm_ClauseBound_Rec_sum_choose_le
-- name    : ClauseBound.Rec.sum_choose_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:44:15.520132+00:00
-- url     : https://prove2.me/theorems/68ac81e9-70e5-4624-8aba-258d0798cc61
-- title:
--   Rec: sum choose le
-- statement:
--   For 1 ≤ n ≤ δ: Σ_{ν≤n} C(δ, ν) ≤ (3δ/n)^n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/Few.lean#L46-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/Few.lean#L46-L63

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

theorem ClauseBound.Rec.sum_choose_le {δ n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ δ) :
    (∑ ν ∈ range (n + 1), (δ.choose ν : ℝ)) ≤ (3 * δ / n) ^ n := by sorry
