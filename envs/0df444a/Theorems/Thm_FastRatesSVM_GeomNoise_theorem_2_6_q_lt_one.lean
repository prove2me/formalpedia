-- Prove2me | Theorems.Thm_FastRatesSVM_GeomNoise_theorem_2_6_q_lt_one
-- name    : FastRatesSVM.GeomNoise.theorem_2_6_q_lt_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:54:20.073882+00:00
-- url     : https://prove2.me/theorems/2d79068a-5d3c-4ef1-9428-0cdf3c21a0c3
-- title:
--   Theorem 2.6, case $0 \le q < 1$ — envelope $\gamma$ + Tsybakov $q$ give geometric noise exponent $\alpha$ for all $\alpha < (q+1)\gamma/d$
-- statement:
--   Let $d \ge 1$, let $X \subset \mathbb R^d$ be compact, and let $P$ be a distribution on $X \times \{-1, 1\}$ with marginal $P_X$ and measurable regression function $\eta$ with values in $[0,1]$. Suppose that $P$ has an envelope of order $\gamma > 0$ (Definition 2.5) and Tsybakov noise exponent $q$ with $0 \le q < 1$ (Definition 2.2). Then for every $\alpha$ with
--
--   $$0 < \alpha < \frac{(q+1)\gamma}{d},$$
--
--   $P$ has geometric noise exponent $\alpha$ (Definition 2.3).
--
--   This is the second clause of Theorem 2.6: for small Tsybakov exponents the envelope condition yields every geometric noise exponent below the critical value $(q+1)\gamma/d$.
--
--   **Formalization Note** The restriction $\alpha > 0$ is the range of Definition 2.3, where geometric noise exponents are positive. $d \ge 1$ is added because the exponent divides by $d$. $P$ is represented by $\mu = P_X$, a probability measure on `EuclideanSpace ℝ (Fin d)` with $\mu(X^c) = 0$, and a measurable version $\eta : \mathbb R^d \to [0,1]$ of the regression function; every Borel distribution on $X \times \{-1,1\}$ has this form. The convention $d(x, \emptyset) := 0$ of equation (7) applies. The paper's proof ends "for the case $0 < q < 1$"; the statement, and the argument, cover $q = 0$.
-- source:
--   Steinwart, Scovel, Fast Rates for Support Vector Machines Using Gaussian Kernels, arXiv:0708.1838v1, p. 8, Theorem 2.6 (second clause); proof pp. 18-19

import Mathlib
import Definitions.Def_FastRatesSVM_GeomNoise_Tau
import Definitions.Def_FastRatesSVM_GeomNoise_TsybakovNoise
import Definitions.Def_FastRatesSVM_GeomNoise_GeometricNoise
import Definitions.Def_FastRatesSVM_GeomNoise_Envelope

open MeasureTheory

namespace FastRatesSVM.GeomNoise

theorem theorem_2_6_q_lt_one
    {d : ℕ} (hd : 0 < d) (X : Set (EuclideanSpace ℝ (Fin d))) (hX : IsCompact X)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (hμX : μ Xᶜ = 0)
    (η : EuclideanSpace ℝ (Fin d) → ℝ) (hη : Measurable η) (hη01 : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (γ q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (henv : HasEnvelope X μ η γ)
    (hts : HasTsybakovNoiseExponent X μ η (ENNReal.ofReal q)) :
    ∀ α : ℝ, 0 < α → α < (q + 1) * γ / d → HasGeometricNoiseExponent X μ η α := by sorry

end FastRatesSVM.GeomNoise
