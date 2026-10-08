-- Prove2me | Theorems.Thm_FastRatesSVM_GeomNoise_tau_estimate
-- name    : FastRatesSVM.GeomNoise.tau_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:51:26.784361+00:00
-- url     : https://prove2.me/theorems/360bbb21-9211-47d3-84c1-c37e92ab1327
-- title:
--   Proof of Theorem 2.6, p. 19 — $\tau^{q+1} = \exp(-(\tau/c_\gamma)^{2/\gamma}t^{-1})$ implies $\tau \le (\hat a\gamma/2)^{\gamma/2}(t\ln\frac1{\hat at})^{\gamma/2}$
-- statement:
--   Let $c_\gamma > 0$, $\gamma > 0$ and $q \ge 0$, and put $\hat a := (c_\gamma)^{2/\gamma}(q + 1)$. For $t > 0$ consider the equation in $\tau > 0$
--
--   $$\tau^{q+1} = \exp\Big(-\Big(\frac{\tau}{c_\gamma}\Big)^{2/\gamma} t^{-1}\Big).$$
--
--   There is $t_0 > 0$, depending only on $c_\gamma$, $\gamma$ and $q$, such that for every $t \in (0, t_0)$ the equation has a solution $\tau > 0$, and every solution satisfies
--
--   $$\tau \le \Big(\frac{\hat a\gamma}{2}\Big)^{\gamma/2}\Big(t \ln\frac{1}{\hat a t}\Big)^{\gamma/2}.$$
--
--   This is the choice of the splitting level $\tau$ in display (33): it balances the two terms there, and the resulting bound $(C+1)\tau^{q+1}$ decays like $(t\ln(1/t))^{\gamma(q+1)/2}$, which yields every geometric noise exponent $\alpha < (q+1)\gamma/d$.
--
--   **Formalization Note** The page writes "Let us define $\tau$ by … For $\hat a := \ldots$ and small $t$ this definition implies …". "Small $t$" is the threshold $t_0$, chosen before $t$ and $\tau$. The existence of a solution, presupposed by "define $\tau$ by", is stated as the first conjunct; the inequality is stated for every positive solution. For $t < t_0$ one has $\hat a t < 1$, so the logarithm is positive.
-- source:
--   Steinwart, Scovel, Fast Rates for Support Vector Machines Using Gaussian Kernels, arXiv:0708.1838v1, p. 19, §4.2, proof of Theorem 2.6, display after (33)

import Mathlib

namespace FastRatesSVM.GeomNoise

theorem tau_estimate (γ q cγ : ℝ) (hγ : 0 < γ) (hq : 0 ≤ q) (hcγ : 0 < cγ) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ →
      (∃ τ : ℝ, 0 < τ ∧ τ ^ (q + 1) = Real.exp (-(τ / cγ) ^ (2 / γ) * t⁻¹)) ∧
      ∀ τ : ℝ, 0 < τ → τ ^ (q + 1) = Real.exp (-(τ / cγ) ^ (2 / γ) * t⁻¹) →
        τ ≤ (cγ ^ (2 / γ) * (q + 1) * γ / 2) ^ (γ / 2) *
          (t * Real.log (1 / (cγ ^ (2 / γ) * (q + 1) * t))) ^ (γ / 2) := by sorry

end FastRatesSVM.GeomNoise
