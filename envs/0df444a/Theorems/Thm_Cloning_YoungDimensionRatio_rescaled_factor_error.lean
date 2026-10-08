-- Prove2me | Theorems.Thm_Cloning_YoungDimensionRatio_rescaled_factor_error
-- name    : Cloning.YoungDimensionRatio.rescaled_factor_error
-- status  : Proved
-- author  : @JWang226
-- created : 2026-10-07T18:49:37.045491+00:00
-- url     : https://prove2.me/theorems/2356e1d1-37d8-4543-9b6e-0ed2afd7d9f6
-- title:
--   Uniform error bound for one rescaled crossing-root factor
-- statement:
--   Let $r,k$ be nonnegative integers with $r>0$, let $N>0$ and $\delta$ be real, and let $\mathrm{row}:\mathrm{Fin}(r)\to\mathbb R$ satisfy $|\mathrm{row}_i/N-1/r|\le\delta$ for every $i<r$. For every $i<r,j<k$, with $g_{i,j}=r+j-i$,
--
--   $$\left|\frac{r(\mathrm{row}_i+g_{i,j})}{N}-1\right|\le r\delta+\frac{r(r+k)}{N}.$$
--
--   The estimate separates row-proportion error from the finite crossing-root gap.
--
--   This is supporting analytic material for [the paper](https://arxiv.org/abs/2609.35986).
-- source:
--   https://github.com/JWang226/Cloning/blob/cb7b0df616294bd0729dd1ad693421739f01fd0b/formalization/Cloning/YoungDimensionRatio.lean#L78-L100

import Definitions.Def_Cloning_YoungDimensionRatio
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Concrete asymptotics of the crossing-root Weyl dimension product

For an `r`-row label in ambient dimension `r+k`, the manuscript's explicit
dimension-ratio expression is the product of `(rowᵢ+j-i)/(j-i)` over crossing
roots. This file defines that actual finite product and derives its uniform
relative-error bound directly from the row lengths. No dimension-ratio
convergence or product approximation is assumed.

The identification of this explicit Weyl product with dimensions of the
particular representation spaces is a separate representation-theoretic
statement. This file proves the analytic input once that formula is used.
-/


open scoped BigOperators Topology
open Filter

open Cloning.YoungDimensionRatio

theorem Cloning.YoungDimensionRatio.rescaled_factor_error (r k : ℕ) (row : Fin r → ℝ) (N δ : ℝ)
    (hr : 0 < r) (hN : 0 < N)
    (hclose : ∀ i, |row i / N - 1 / (r : ℝ)| ≤ δ) (a : Fin r × Fin k) :
    |(r : ℝ) * (row a.1 + crossingGap a) / N - 1| ≤
      (r : ℝ) * δ + (r : ℝ) * ((r : ℝ) + k) / N := by sorry
