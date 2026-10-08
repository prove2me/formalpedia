-- Prove2me | Theorems.Thm_FastRatesSVM_GeomNoise_display_33
-- name    : FastRatesSVM.GeomNoise.display_33
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:52:30.793676+00:00
-- url     : https://prove2.me/theorems/bc49a6d3-2d62-4d1e-89d0-39778ee00a2e
-- title:
--   Proof of Theorem 2.6, display (33) — $\mathbb E|2\eta-1|e^{-\tau_x^2/t} \le C\tau^{q+1} + \exp(-(\tau/c_\gamma)^{2/\gamma}t^{-1})$
-- statement:
--   Let $X \subset \mathbb R^d$ be compact and let $P$ be a distribution on $X \times \{-1,1\}$ with marginal $P_X$, a measurable regression function $\eta$ with values in $[0,1]$, and distance to the decision boundary $\tau_x$ (equation (7)). Let $q \ge 0$ and $C > 0$ be such that the Tsybakov bound holds for all $s > 0$:
--
--   $$P_X\big(\{x \in X : |2\eta(x) - 1| \le s\}\big) \le C s^q \qquad (s > 0),$$
--
--   and let $\gamma > 0$ and $c_\gamma > 0$ be such that $|2\eta(x) - 1| \le c_\gamma \tau_x^\gamma$ for $P_X$-almost all $x \in X$. Then for all $t > 0$ and $\tau \ge 0$
--
--   $$\mathbb E_{x \sim P_X}\Big(|2\eta(x) - 1|\, e^{-\tau_x^2/t}\Big) \le C\tau^{q+1} + \exp\Big(-\Big(\frac{\tau}{c_\gamma}\Big)^{2/\gamma} t^{-1}\Big).$$
--
--   The bound splits the expectation at the level $\tau$ of $|2\eta - 1|$: the noise condition controls the small values, the envelope condition the large ones. Optimizing over $\tau$ gives the geometric noise exponent in the case $0 \le q < 1$ of Theorem 2.6.
--
--   **Formalization Note** The paper states (33) for $t, \tau \ge 0$ inside the case $0 \le q < 1$; here $t > 0$ (at $t = 0$ the term $t^{-1}$ is undefined) and the bound is stated for every $q \ge 0$, where it holds verbatim. The Tsybakov hypothesis is the all-$t$ form of (5), which by the remark on p. 6 is equivalent to Definition 2.2 for $q < \infty$ up to the constant; the envelope hypothesis is (10) with its constant $c_\gamma$ named. The expectation is the $[0,\infty]$-valued Lebesgue integral of the nonnegative integrand; the paper's middle step, which splits the integral into the parts $|2\eta - 1| \le \tau$ and $> \tau$, is not stated separately. Measurability of $\eta$ and $\eta \in [0,1]$ everywhere are the standing properties of a regression function. The convention $d(x, \emptyset) := 0$ of equation (7) applies.
-- source:
--   Steinwart, Scovel, Fast Rates for Support Vector Machines Using Gaussian Kernels, arXiv:0708.1838v1, pp. 18-19, §4.2, proof of Theorem 2.6, display (33)

import Mathlib
import Definitions.Def_FastRatesSVM_GeomNoise_Tau

open MeasureTheory

namespace FastRatesSVM.GeomNoise

theorem display_33
    {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d))) (hX : IsCompact X)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (hμX : μ Xᶜ = 0)
    (η : EuclideanSpace ℝ (Fin d) → ℝ) (hη : Measurable η) (hη01 : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (q C : ℝ) (hq : 0 ≤ q) (hC : 0 < C)
    (hts : ∀ s : ℝ, 0 < s → μ {x | x ∈ X ∧ |2 * η x - 1| ≤ s} ≤ ENNReal.ofReal (C * s ^ q))
    (γ cγ : ℝ) (hγ : 0 < γ) (hcγ : 0 < cγ)
    (henv : ∀ᵐ x ∂μ, x ∈ X → |2 * η x - 1| ≤ cγ * tau X η x ^ γ)
    (t τ : ℝ) (ht : 0 < t) (hτ : 0 ≤ τ) :
    (∫⁻ x, ENNReal.ofReal (|2 * η x - 1| * Real.exp (-(tau X η x) ^ 2 / t)) ∂μ) ≤
      ENNReal.ofReal (C * τ ^ (q + 1) + Real.exp (-(τ / cγ) ^ (2 / γ) * t⁻¹)) := by sorry

end FastRatesSVM.GeomNoise
