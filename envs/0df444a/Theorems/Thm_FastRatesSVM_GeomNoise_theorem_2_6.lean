-- Prove2me | Theorems.Thm_FastRatesSVM_GeomNoise_theorem_2_6
-- name    : FastRatesSVM.GeomNoise.theorem_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:54:32.673978+00:00
-- url     : https://prove2.me/theorems/a135d7c1-d79f-40c9-af3e-ebcf9ac83b3e
-- title:
--   Theorem 2.6 — envelope of order $\gamma$ and Tsybakov noise exponent $q$ give geometric noise exponent $(q+1)\gamma/d$
-- statement:
--   Let $d \ge 1$, let $X \subset \mathbb R^d$ be compact, and let $P$ be a distribution on $X \times \{-1, 1\}$ with marginal $P_X$ and measurable regression function $\eta$ with values in $[0,1]$. Suppose that $P$ has an envelope of order $\gamma > 0$ (Definition 2.5) and a Tsybakov noise exponent $q \in [0, \infty)$ (Definition 2.2). Then:
--
--   1. if $q \ge 1$, $P$ has geometric noise exponent $\dfrac{(q+1)\gamma}{d}$;
--   2. if $0 \le q < 1$, $P$ has geometric noise exponent $\alpha$ for every $\alpha$ with $0 < \alpha < \dfrac{(q+1)\gamma}{d}$.
--
--   Here geometric noise exponent $\alpha$ (Definition 2.3) means
--
--   $$\int_X |2\eta(x) - 1| \exp\Big(-\frac{\tau_x^2}{t}\Big)\,P_X(dx) \le C\,t^{\alpha d/2}, \qquad t > 0,$$
--
--   for some constant $C > 0$, with $\tau_x$ the distance of $x$ to the decision boundary (equation (7)).
--
--   The theorem converts two standard regularity assumptions, a pointwise envelope on $\eta$ near the decision boundary and a bound on the mass of the noisy region, into the geometric noise exponent that controls the approximation error of Gaussian-kernel support vector machines, and hence into explicit learning rates.
--
--   **Formalization Note** $d \ge 1$ is added because the exponent divides by $d$; $\alpha > 0$ in clause 2 is the range of Definition 2.3. $P$ is represented by $\mu = P_X$, a probability measure on `EuclideanSpace ℝ (Fin d)` with $\mu(X^c) = 0$, and a measurable version $\eta : \mathbb R^d \to [0,1]$ of the regression function $P(y = 1 \mid x)$; every Borel distribution on $X \times \{-1, 1\}$ has this form, and the paper defines $\tau_x$ "for some choice of $\eta$". The paper leaves $d(x,\emptyset)$ unspecified; the convention $d(x,\emptyset) := 0$ (Lean's `Metric.infDist`) is used, and the statement is true under either reading. The Tsybakov exponent $q$ is a real number $\ge 0$, passed to Definition 2.2 as an element of $[0,\infty]$.
-- source:
--   Steinwart, Scovel, Fast Rates for Support Vector Machines Using Gaussian Kernels, arXiv:0708.1838v1, p. 8, Theorem 2.6; proof §4.2, pp. 17-19

import Mathlib
import Definitions.Def_FastRatesSVM_GeomNoise_Tau
import Definitions.Def_FastRatesSVM_GeomNoise_TsybakovNoise
import Definitions.Def_FastRatesSVM_GeomNoise_GeometricNoise
import Definitions.Def_FastRatesSVM_GeomNoise_Envelope

open MeasureTheory

namespace FastRatesSVM.GeomNoise

theorem theorem_2_6
    {d : ℕ} (hd : 0 < d) (X : Set (EuclideanSpace ℝ (Fin d))) (hX : IsCompact X)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (hμX : μ Xᶜ = 0)
    (η : EuclideanSpace ℝ (Fin d) → ℝ) (hη : Measurable η) (hη01 : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (γ q : ℝ) (hq : 0 ≤ q)
    (henv : HasEnvelope X μ η γ)
    (hts : HasTsybakovNoiseExponent X μ η (ENNReal.ofReal q)) :
    (1 ≤ q → HasGeometricNoiseExponent X μ η ((q + 1) * γ / d)) ∧
    (q < 1 → ∀ α : ℝ, 0 < α → α < (q + 1) * γ / d → HasGeometricNoiseExponent X μ η α) := by sorry

end FastRatesSVM.GeomNoise
