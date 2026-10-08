-- Prove2me | Theorems.Thm_AdamDyn_DecConv_remainder_tendsto_zero
-- name    : AdamDyn.DecConv.remainder_tendsto_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:21:18.460578+00:00
-- url     : https://prove2.me/theorems/11d3703d-3523-4490-a94d-1babf5cdcc1d
-- title:
--   §9.1 — the remainder $\varsigma_n$ of the perturbed Euler decomposition converges to $0$ a.s.
-- statement:
--   Let $(\Omega, \mathcal F, \mathbb P)$ be a probability space, $\xi$ a random variable with law $\mu$ on $\Xi$, $f$ an integrand with gradient $\nabla f$, and $F$, $S$, $\mathcal S$ as in (2.2). Let $\varepsilon > 0$ and let $(\gamma_n, \alpha_n, \beta_n)$ satisfy Assumption 5.1 with constants $0 < b < 4a$, with moreover $\alpha_1 < 1$ and $\beta_1 < 1$. Assume Assumption 2.2, Assumption 2.3 ($F$ coercive), Assumption 2.4 ($S(x) > 0$ coordinatewise for all $x$), Assumption 4.1 (the samples $\xi_1, \xi_2, \dots$ are iid with law $\mu$) and Assumption 4.2 i) with $p = 4$. Let $z_n = (x_n, m_n, v_n)$ be the iterates of Algorithm 5.1 from $(x_0, 0, 0)$, and assume that, with probability one, the sequence $(z_n)$ is bounded.
--
--   Let $\varsigma_{n+1}$ be the remainder of §9.1 built from these iterates with $F$, $S$ of (2.2):
--   $$ \varsigma^x_{n+1} = \frac{m_n}{\varepsilon + \sqrt{v_n}} - \frac{\gamma_n}{\gamma_{n+1}} \frac{\hat m_n}{\varepsilon + \sqrt{\hat v_n}}, \quad \varsigma^m_{n+1} = \Big(\tfrac{1 - \alpha_{n+1}}{\gamma_{n+1}} - a\Big)(\nabla F(x_n) - m_n) + a(\nabla F(x_n) - \nabla F(x_{n-1})), $$
--   and $\varsigma^v_{n+1}$ likewise with $S$, $v$, $\beta$, $b$. Then, almost surely,
--   $$ \lim_{n \to \infty} \varsigma_n = 0 . $$
--
--   In the decomposition $\bar z_{n+1} = \bar z_n + \gamma_{n+1} h_\infty(\bar z_n) + \gamma_{n+1}\chi_{n+1} + \gamma_{n+1}\varsigma_{n+1}$ of the shifted iterates $\bar z_n = (x_{n-1}, m_n, v_n)$, this says the drift error is asymptotically negligible, so only the martingale noise $\chi$ remains to be controlled.
--
--   **Formalization Note** The hypotheses are those of Theorem 5.2 except the empty-interior condition on $F(\mathcal S)$, which this step does not use. $\alpha_1 < 1$, $\beta_1 < 1$ make the divisors $r_n$, $\bar r_n$ positive (Lean's division by $0$ returns $0$). The limit is in $\mathcal Z$ with the max-of-factors norm.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, pp. 25–26, §9.1 (proof of Theorem 5.2): definition of ς_{n+1} and "We prove that ς_n → 0 a.s."

import Mathlib
import Definitions.Def_AdamDyn_DecConv_Algorithm
import Definitions.Def_AdamDyn_DecConv_StochasticModel
import Definitions.Def_AdamDyn_DecConv_ProofQuantities

open MeasureTheory Filter Topology

namespace AdamDyn.DecConv

/-- §9.1, proof of Theorem 5.2 (Barakat & Bianchi, arXiv:1810.02263v4, pp. 25–26): under the
hypotheses of Theorem 5.2 (Assumptions 2.2–2.4, 4.1, 5.1, 4.2 i) with `p = 4`, and boundedness
of the iterates of Algorithm 5.1 with probability one), the remainder `ς_n` of the perturbed
Euler decomposition `z̄_{n+1} = z̄_n + γ_{n+1} h∞(z̄_n) + γ_{n+1} χ_{n+1} + γ_{n+1} ς_{n+1}`
converges to `0` almost surely. Here `F` and `S` are those of (2.2). -/
theorem remainder_tendsto_zero {d : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : AdamDyn.WellPosed.Vec d → Ξ → ℝ) (gf : AdamDyn.WellPosed.Vec d → Ξ → AdamDyn.WellPosed.Vec d) (ξ : ℕ → Ω → Ξ)
    (γ α β : ℕ → ℝ) (a b ε : ℝ) (x0 : AdamDyn.WellPosed.Vec d)
    (hε : 0 < ε)
    (h22 : Assumption22 μ f gf)
    (h23 : Tendsto (AdamDyn.ConstStep.objective μ f) (cocompact (AdamDyn.WellPosed.Vec d)) atTop)
    (h24 : ∀ x i, 0 < AdamDyn.ConstStep.sqGradMean μ gf x i)
    (h41 : Assumption41 P μ ξ)
    (h51 : Assumption51 γ α β a b)
    (h42 : Assumption42i μ gf 4)
    (hα1 : α 1 < 1) (hβ1 : β 1 < 1)
    (hbdd : ∀ᵐ ω ∂P, Bornology.IsBounded (Set.range fun n => adamIter gf γ α β ε x0 ξ n ω)) :
    ∀ᵐ ω ∂P, Tendsto (fun n => remainder γ α β a b ε (AdamDyn.ConstStep.objective μ f) (AdamDyn.ConstStep.sqGradMean μ gf)
      (fun k => adamIter gf γ α β ε x0 ξ k ω) n) atTop (𝓝 0) := by sorry

end AdamDyn.DecConv
