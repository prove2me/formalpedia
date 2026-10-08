-- Prove2me | Theorems.Thm_FastRatesSVM_GeomNoise_theorem_2_6_q_ge_one
-- name    : FastRatesSVM.GeomNoise.theorem_2_6_q_ge_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:54:37.18798+00:00
-- url     : https://prove2.me/theorems/15120a2f-3189-4bb6-b6fd-24567069c6b5
-- title:
--   Theorem 2.6, case $q \ge 1$ — envelope $\gamma$ + Tsybakov $q$ give geometric noise exponent $(q+1)\gamma/d$
-- statement:
--   Let $d \ge 1$, let $X \subset \mathbb R^d$ be compact, and let $P$ be a distribution on $X \times \{-1, 1\}$ with marginal $P_X$ and measurable regression function $\eta$ with values in $[0,1]$. Suppose that $P$ has an envelope of order $\gamma > 0$ (Definition 2.5) and Tsybakov noise exponent $q$ with $1 \le q < \infty$ (Definition 2.2). Then $P$ has geometric noise exponent
--
--   $$\alpha = \frac{(q+1)\gamma}{d}$$
--
--   (Definition 2.3), i.e. $\int_X |2\eta - 1| e^{-\tau_x^2/t}\,dP_X \le C t^{(q+1)\gamma/2}$ for all $t > 0$ and some constant $C$.
--
--   This is the first clause of Theorem 2.6: for Tsybakov exponents $q \ge 1$ the critical exponent itself is attained.
--
--   **Formalization Note** $d \ge 1$ is added because the exponent divides by $d$. $P$ is represented by $\mu = P_X$, a probability measure on `EuclideanSpace ℝ (Fin d)` with $\mu(X^c) = 0$, and a measurable version $\eta : \mathbb R^d \to [0,1]$ of the regression function. The convention $d(x, \emptyset) := 0$ of equation (7) applies.
-- source:
--   Steinwart, Scovel, Fast Rates for Support Vector Machines Using Gaussian Kernels, arXiv:0708.1838v1, p. 8, Theorem 2.6 (first clause); proof pp. 17-18

import Mathlib
import Definitions.Def_FastRatesSVM_GeomNoise_Tau
import Definitions.Def_FastRatesSVM_GeomNoise_TsybakovNoise
import Definitions.Def_FastRatesSVM_GeomNoise_GeometricNoise
import Definitions.Def_FastRatesSVM_GeomNoise_Envelope

open MeasureTheory

namespace FastRatesSVM.GeomNoise

theorem theorem_2_6_q_ge_one
    {d : ℕ} (hd : 0 < d) (X : Set (EuclideanSpace ℝ (Fin d))) (hX : IsCompact X)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (hμX : μ Xᶜ = 0)
    (η : EuclideanSpace ℝ (Fin d) → ℝ) (hη : Measurable η) (hη01 : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (γ q : ℝ) (hq : 1 ≤ q)
    (henv : HasEnvelope X μ η γ)
    (hts : HasTsybakovNoiseExponent X μ η (ENNReal.ofReal q)) :
    HasGeometricNoiseExponent X μ η ((q + 1) * γ / d) := by sorry

end FastRatesSVM.GeomNoise
