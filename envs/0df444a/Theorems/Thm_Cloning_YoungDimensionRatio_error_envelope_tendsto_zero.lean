-- Prove2me | Theorems.Thm_Cloning_YoungDimensionRatio_error_envelope_tendsto_zero
-- name    : Cloning.YoungDimensionRatio.error_envelope_tendsto_zero
-- status  : Proved
-- author  : @JWang226
-- created : 2026-10-07T18:49:18.603709+00:00
-- url     : https://prove2.me/theorems/c6e43822-eea9-49ec-bb43-d7ac68f5a70c
-- title:
--   Vanishing error envelope for crossing-root product asymptotics
-- statement:
--   Let $r,k$ be arbitrary nonnegative integers and let $N,\delta:\mathbb N\to\mathbb R$ satisfy $N_n\to+\infty$ and $\delta_n\to0$. Then
--
--   $$\exp\!\left(rk\left[r\delta_n+\frac{r(r+k)}{N_n}\right]\right)-1\longrightarrow0.$$
--
--   No positivity hypothesis on every N_n is needed for this limit; divergence to positive infinity controls the inverse eventually.
--
--   This is supporting analytic material for [the paper](https://arxiv.org/abs/2609.35986).
-- source:
--   https://github.com/JWang226/Cloning/blob/cb7b0df616294bd0729dd1ad693421739f01fd0b/formalization/Cloning/YoungDimensionRatio.lean#L136-L153

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

theorem Cloning.YoungDimensionRatio.error_envelope_tendsto_zero (r k : ℕ) (N δ : ℕ → ℝ)
    (hN : Tendsto N atTop atTop) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n =>
      Real.exp ((r * k : ℕ) * ((r : ℝ) * δ n + (r : ℝ) * ((r : ℝ) + k) / N n)) - 1)
      atTop (𝓝 0) := by sorry
