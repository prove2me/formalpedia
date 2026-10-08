-- Prove2me | Theorems.Thm_ErlangA_Diffusion_infinitesimal_moments_limit
-- name    : ErlangA.Diffusion.infinitesimal_moments_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:03:06.559867+00:00
-- url     : https://prove2.me/theorems/3f52ac77-0496-4ca4-b295-dd249e2c2e44
-- title:
--   App. C, p. 224 — infinitesimal mean and variance of $q_N$ converge to $f(x)$ and $2\mu$
-- statement:
--   Let $\mu > 0$, $\beta \in \mathbb R$ and $0 < \theta < \infty$. Let $(\lambda_N)$ and $(\theta_N)$ be real sequences with
--   $$
--   \lim_{N\to\infty} \sqrt N\Big(1 - \frac{\lambda_N}{N\mu}\Big) = \beta, \qquad \lim_{N\to\infty}\theta_N = \theta .
--   $$
--   Let $\mu_N(x)$ and $\sigma_N^2(x)$ be the infinitesimal expectation and variance of the scaled Erlang-A queue (Appendix C, p. 224). Then for every $x \in \mathbb R$,
--   $$
--   \lim_{N\to\infty}\mu_N(x) = f(x) = \begin{cases} -\mu(\beta + x), & x \le 0,\\ -(\mu\beta + \theta x), & x > 0,\end{cases}
--   \qquad
--   \lim_{N\to\infty}\sigma_N^2(x) = 2\mu .
--   $$
--
--   The limits are the drift and the squared diffusion coefficient of the limit diffusion $dq = f(q)\,dt + \sqrt{2\mu}\,db$ of Theorem 2; their convergence is the input to Stone's criteria in the paper's proof.
--
--   **Formalization Note** The paper prints this display for the case $\theta = 0$, where the limit drift on $x > 0$ is $-\mu\beta$, and says the case $0 < \theta < \infty$ "can be proved either as in the case $\theta = 0$". This item is the $0 < \theta < \infty$ instance: the same $\mu_N$, $\sigma_N^2$, with the limit $f$ of Theorem 2. The convergence is pointwise in $x$, as printed.
-- source:
--   Garnett, Mandelbaum & Reiman, Designing a Call Center with Impatient Customers, M&SOM 4(3), 2002, p. 224, App. C, proof of Theorem 2*, Part 1 (case 0 < θ < ∞ of the displayed limits)

import Mathlib
import Definitions.Def_ErlangA_Diffusion_SDE
import Definitions.Def_ErlangA_Diffusion_InfinitesimalMoments

open Filter Topology

namespace ErlangA.Diffusion

/-- Appendix C, proof of Theorem 2*, Part 1 (p. 224), case `0 < θ < ∞`: if
`√N (1 − λ_N/(Nμ)) → β` and `θ_N → θ ∈ (0, ∞)`, then for every `x ∈ ℝ` the infinitesimal
expectation `μ_N(x)` tends to the drift `f(x)` of Theorem 2 and the infinitesimal variance
`σ_N²(x)` tends to `2μ`. -/
theorem infinitesimal_moments_limit (μ β θ : ℝ) (hμ : 0 < μ) (hθ : 0 < θ)
    (lam thetaN : ℕ → ℝ)
    (hβ : Tendsto (fun N : ℕ => Real.sqrt N * (1 - lam N / (N * μ))) atTop (𝓝 β))
    (hθN : Tendsto thetaN atTop (𝓝 θ)) (x : ℝ) :
    Tendsto (fun N : ℕ => infMean lam thetaN μ N x) atTop (𝓝 (drift μ β θ x)) ∧
    Tendsto (fun N : ℕ => infVar lam thetaN μ N x) atTop (𝓝 (2 * μ)) := by sorry

end ErlangA.Diffusion
