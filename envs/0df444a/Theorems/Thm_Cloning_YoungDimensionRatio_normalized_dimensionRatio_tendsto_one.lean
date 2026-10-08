-- Prove2me | Theorems.Thm_Cloning_YoungDimensionRatio_normalized_dimensionRatio_tendsto_one
-- name    : Cloning.YoungDimensionRatio.normalized_dimensionRatio_tendsto_one
-- status  : Proved
-- author  : @JWang226
-- created : 2026-10-07T18:50:34.71775+00:00
-- url     : https://prove2.me/theorems/b1b00c4d-f996-4b44-834e-5da1e96bc044
-- title:
--   Leading asymptotics of the explicit crossing-root dimension product
-- statement:
--   Let $r,k$ be nonnegative integers with $r>0$, and let $\mathrm{row}:\mathbb N\to(\mathrm{Fin}(r)\to\mathbb R)$ and $N,\delta:\mathbb N\to\mathbb R$. Assume $N_n>0$ for every n, $N_n\to+\infty$, $\delta_n\to0$, and $|\mathrm{row}_{n,i}/N_n-1/r|\le\delta_n$ for every n and i<r. For $D_{r,k}(\mathrm{row})=\prod_{i<r,j<k}(\mathrm{row}_i+r+j-i)/(r+j-i)$ and $c_{r,k}=\prod_{i<r,j<k}1/[r(r+j-i)]$,
--
--   $$\frac{D_{r,k}(\mathrm{row}_n)}{c_{r,k}N_n^{rk}}\longrightarrow1.$$
--
--   This is supporting analytic asymptotics for the explicit finite product. It does not identify that product with representation dimensions or prove the complete mixed-state cloning theorem.
--
--   This is supporting analytic material for [the paper](https://arxiv.org/abs/2609.35986).
-- source:
--   https://github.com/JWang226/Cloning/blob/cb7b0df616294bd0729dd1ad693421739f01fd0b/formalization/Cloning/YoungDimensionRatio.lean#L155-L170

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

theorem Cloning.YoungDimensionRatio.normalized_dimensionRatio_tendsto_one (r k : ℕ) (hr : 0 < r)
    (row : ℕ → Fin r → ℝ) (N δ : ℕ → ℝ)
    (hNpos : ∀ n, 0 < N n) (hN : Tendsto N atTop atTop)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hclose : ∀ n i, |row n i / N n - 1 / (r : ℝ)| ≤ δ n) :
    Tendsto (fun n => dimensionRatio r k (row n) /
      (leadingConstant r k * (N n) ^ (r * k))) atTop (𝓝 1) := by sorry
