-- Prove2me | Theorems.Thm_Cloning_YoungDimensionRatio_dimensionRatio_factorization
-- name    : Cloning.YoungDimensionRatio.dimensionRatio_factorization
-- status  : Proved
-- author  : @JWang226
-- created : 2026-10-07T18:49:02.512792+00:00
-- url     : https://prove2.me/theorems/974e9cc4-546c-4890-ab27-fd362b066f2c
-- title:
--   Exact factorization of the crossing-root dimension product
-- statement:
--   Let $r,k$ be nonnegative integers with $r>0$, let $N>0$ be real, and let $\mathrm{row}:\mathrm{Fin}(r)\to\mathbb R$ be arbitrary. For $g_{i,j}=r+j-i$, define $D_{r,k}(\mathrm{row})=\prod_{i<r,j<k}(\mathrm{row}_i+g_{i,j})/g_{i,j}$ and $c_{r,k}=\prod_{i<r,j<k}1/(r g_{i,j})$. Then
--
--   $$D_{r,k}(\mathrm{row})=c_{r,k}N^{rk}\prod_{i<r,j<k}\frac{r(\mathrm{row}_i+g_{i,j})}{N}.$$
--
--   This is an exact algebraic identity for the explicit product. Its identification with representation dimensions is a separate theorem.
--
--   This is supporting analytic material for [the paper](https://arxiv.org/abs/2609.35986).
-- source:
--   https://github.com/JWang226/Cloning/blob/cb7b0df616294bd0729dd1ad693421739f01fd0b/formalization/Cloning/YoungDimensionRatio.lean#L60-L76

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

theorem Cloning.YoungDimensionRatio.dimensionRatio_factorization (r k : ℕ) (row : Fin r → ℝ) (N : ℝ)
    (hr : 0 < r) (hN : 0 < N) :
    dimensionRatio r k row = leadingConstant r k * N ^ (r * k) *
      ∏ a : Fin r × Fin k, ((r : ℝ) * (row a.1 + crossingGap a) / N) := by sorry
