-- Prove2me | Theorems.Thm_DROCalibration_Sensitivity_cstar_tendsto
-- name    : DROCalibration.Sensitivity.cstar_tendsto
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:23.046516+00:00
-- url     : https://prove2.me/theorems/a2cc204c-01e1-491a-9992-8a578e4b32df
-- title:
--   (F.7)–(F.8), p. 49 — the multiplier c⋆(δ) exists, is locally unique, and tends to −𝔼_{ℙn}[f] as δ ↓ 0
-- statement:
--   Fix a decision $x$, nominal probabilities $p_i>0$ with $\sum_i p_i=1$ (the empirical distribution is $p_i=1/n$) and rewards $f_i=f(x,Y_i)$, and let $E=\mathbb E_{\mathbb P_n}[f]=\sum_ip_if_i$. Let $\phi$ satisfy Assumption 2.1 and let $\phi^*$ be its convex conjugate. Then there are $\delta_0>0$ and $r>0$ such that:
--
--   1. for every $\delta\in(0,\delta_0)$ the first-order condition (F.7)
--   $$\sum_{i=1}^n p_i\,[\phi^*]'\big(\delta(-f_i-c)\big)=1$$
--   has exactly one solution $c=c^\star(\delta)$ in the interval $(-E-r,-E+r)$;
--   2. these solutions converge to the value at $\delta=0$:
--   $$\lim_{\delta\downarrow0}c^\star(\delta)=-\mathbb E_{\mathbb P_n}[f].$$
--
--   The multiplier $c^\star(\delta)$ is the maximizer of the dual problem (F.2) of the inner minimization in (2.7); its limit $-\mathbb E_{\mathbb P_n}[f]$ is what makes the first-order term of the worst-case distribution in (F.3) centered.
--
--   **Formalization Note** This is a corrected reading of the paper. The paper asserts, via the implicit function theorem, that $c^\star$ is continuously differentiable in a neighbourhood of $\delta=0$, and later uses $c^\star(\delta)=-\mathbb E_{\mathbb P_n}[f]+O(\delta)$. Under Assumption 2.1, which gives only $C^2$ smoothness of $\phi$ near $1$, this is false: for $\phi(z)=(z-1)^2+|z-1|^{5/2}$ on $[0,\infty)$, $p=(0.2,0.3,0.5)$ and $f=(0,1,-2)$ one finds numerically $c^\star(\delta)+E\approx0.036\sqrt\delta$. The statement therefore claims existence, local uniqueness and continuity at $\delta=0$ only, which is all that (F.3) and Theorem 2.2 use; no hypothesis is added. Any choice of solutions $\delta\mapsto c^\star(\delta)$ in the interval converges. $[\phi^*]'$ is the derivative of the real part of $\phi^*$.
-- source:
--   Gotoh, Kim & Lim, Calibration of Distributionally Robust Empirical Optimization Models, arXiv:1711.06565v2, p. 49, Appendix F, proof of Proposition F.1, (F.7)–(F.8)

import Mathlib
import Definitions.Def_DROCalibration_Sensitivity_Setting

open Filter Topology

namespace DROCalibration.Sensitivity

theorem cstar_tendsto (φ : ℝ → EReal) (hφ : Assumption21 φ) {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1) (f : Fin n → ℝ) :
    ∃ δ₀ > 0, ∃ r > 0,
      (∀ δ ∈ Set.Ioo 0 δ₀, ∃! c : ℝ, c ∈ Set.Ioo (-wMean p f - r) (-wMean p f + r) ∧
        ∑ i, p i * deriv (conjReal φ) (δ * (-f i - c)) = 1) ∧
      ∀ cs : ℝ → ℝ, (∀ δ ∈ Set.Ioo 0 δ₀, cs δ ∈ Set.Ioo (-wMean p f - r) (-wMean p f + r) ∧
          ∑ i, p i * deriv (conjReal φ) (δ * (-f i - cs δ)) = 1) →
        Tendsto cs (𝓝[>] 0) (𝓝 (-wMean p f)) := by sorry

end DROCalibration.Sensitivity
