-- Prove2me | Theorems.Thm_EquilibriumExperiment_Gradient_theorem_6
-- name    : EquilibriumExperiment.Gradient.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:39:43.915551+00:00
-- url     : https://prove2.me/theorems/2c69e45a-e5b9-4a21-aaec-b037fcd80226
-- title:
--   Theorem 6, p. 21 — with perturbations ζ_n = ζn^{-α}, 0 < α < 1/2, the local-experimentation estimate Γ̂ converges in probability to d/dp u_a(p)
-- statement:
--   Consider a market satisfying the standing assumptions (Definition 5, Assumptions 1–3, (3.1)–(3.2)), conditional on a global state $A = a$. Fix a payment $p > 0$ with $\mathbb E[f_B(p\,\bar\omega)] > 0$, where $\bar\omega = \sup_{x\ge0}\omega(x)$, and constants $\zeta > 0$ and $0 < \alpha < 1/2$. In the $n$-th system, pay supplier $i$ the amount $P_i = p + \zeta_n\varepsilon_i$ with independent signs $\varepsilon_i = \pm1$ and $\zeta_n = \zeta n^{-\alpha}$, let suppliers respond in equilibrium, and observe the scaled demand $\bar D = D/n$ and the participation decisions $Z_i$. From these form the regression coefficient $\hat\Delta$ of (4.1), the interference-corrected estimate
--   $$\hat\Upsilon = \hat\Delta\Big/\Bigl(1 + \frac{p\bar D\hat\Delta\,\omega'(\bar D/\bar Z)}{\bar Z^2\,\omega(\bar D/\bar Z)}\Bigr) \quad (4.2)$$
--   and the utility-gradient estimate
--   $$\hat\Gamma = \hat\Upsilon\Bigl[r\bigl(\bar D/\bar Z\bigr) - p\,\omega\bigl(\bar D/\bar Z\bigr) - \bigl(r'(\bar D/\bar Z) - p\,\omega'(\bar D/\bar Z)\bigr)\bar D/\bar Z\Bigr] - \omega\bigl(\bar D/\bar Z\bigr)\bar Z. \quad (4.3)$$
--   Then for every $\varepsilon > 0$,
--   $$\lim_{n\to\infty}\mathbb P\Bigl[\Bigl|\hat\Gamma - \frac{d}{dp}u(p)\Bigr| > \varepsilon\Bigr] = 0, \quad (4.4)$$
--   where $u(p) = (r(d/\mu(p)) - p\,\omega(d/\mu(p)))\,\mu(p)$ is the mean-field platform utility (3.15).
--
--   The theorem says that small, symmetric, unit-level payment perturbations, whose size vanishes with the market, consistently estimate the gradient of the platform's equilibrium utility, even though every supplier's decision interferes with every other's through the shared matching.
--
--   **Formalization Note** The statement is conditional on one global state $A = a$; because the state space is finite and its law does not depend on $n$, the paper's unconditional probability is the finite mixture $\sum_a \mathbb P(A = a)\,\mathbb P[\cdot \mid A = a]$, so the conditional statement for every $a$ implies (4.4). The positivity condition $\mathbb E[f_B(p\bar\omega)] > 0$ is exactly the condition under which $\mu(p)$ exists (see Lemma 2). $\frac{d}{dp}u(p)$ is Lean's `deriv`; Proposition 12 shows that $u$ is differentiable at $p$, so the value is the true derivative. Lemma 1's requirement $\zeta_n < p$ holds for all large $n$. Each $n$ has its own sample space, so convergence in probability is a limit of the measures of the deviation sets rather than `TendstoInMeasure`. Divisions by zero in (4.1)–(4.3) occur only on events of vanishing probability.
-- source:
--   Wager & Xu, Experimenting in Equilibrium, arXiv:1903.02124v5, p. 21, Theorem 6, eqs. (4.1)–(4.4); proof in Appendix A.4, pp. 37–39

import Mathlib
import Definitions.Def_EquilibriumExperiment_Gradient_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace EquilibriumExperiment.Gradient

theorem theorem_6 {B : Type} [MeasurableSpace B] (M : Market B) (hM : M.Standing)
    {p : ℝ} (hp : 0 < p) (hpos : 0 < ∫ b, M.f b (p * M.omegaSup) ∂M.β)
    {ζ α : ℝ} (hζ : 0 < ζ) (hα : 0 < α) (hα' : α < 1 / 2) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => M.sample n (perturbLaw p (ζ * (n : ℝ) ^ (-α)))
        {x | ε < |M.GammaHat n p (ζ * (n : ℝ) ^ (-α)) x - deriv M.u p|}) atTop (𝓝 0) := by sorry

end EquilibriumExperiment.Gradient
