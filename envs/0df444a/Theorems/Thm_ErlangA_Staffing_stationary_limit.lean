-- Prove2me | Theorems.Thm_ErlangA_Staffing_stationary_limit
-- name    : ErlangA.Staffing.stationary_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:08:47.022665+00:00
-- url     : https://prove2.me/theorems/ff8c625e-f5b4-4799-a97c-a07acbd6f5cf
-- title:
--   Proof of Theorem 2*, Part 2 (Lhs) — the scaled stationary Erlang-A queue converges weakly to the law with density $f$
-- statement:
--   Consider a sequence of Erlang-A queues indexed by the number of agents $N\ge1$: the $N$-th has arrival rate $\lambda_N>0$, service rate $\mu>0$ (fixed) and patience rate $\theta_N>0$. Let $\rho_N=\lambda_N/(N\mu)$ and let $\pi^{(N)}$ be the stationary distribution of the number in system $Q_N(\infty)$. Assume the square-root (QED) scaling and convergent patience,
--   $$
--   \lim_{N\to\infty}\sqrt N(1-\rho_N)=\beta\in\mathbb R,\qquad \lim_{N\to\infty}\theta_N=\theta\in(0,\infty).
--   $$
--   Then the scaled stationary queue $q_N(\infty)=(Q_N(\infty)-N)/\sqrt N$ converges in distribution to the law with density $f$: for every $x\in\mathbb R$,
--   $$
--   \lim_{N\to\infty}P\Bigl\{\frac{Q_N(\infty)-N}{\sqrt N}\le x\Bigr\}=\int_{-\infty}^{x}f(t)\,dt,
--   $$
--   where, with $c=\sqrt{\theta/\mu}\,h(\beta\sqrt{\mu/\theta})\,w(-\beta,\sqrt{\mu/\theta})$, $f(t)=c\,\varphi(t+\beta)/\varphi(\beta)$ for $t\le0$ and $f(t)=c\,\varphi(t\sqrt{\theta/\mu}+\beta\sqrt{\mu/\theta})/\varphi(\beta\sqrt{\mu/\theta})$ for $t>0$.
--
--   The limit is Gaussian-shaped on each side of $0$, with the curvature of the $M/M/N$ queue below $N$ and that of an infinite-server queue with rate $\theta$ above it; it is the stationary input to Lemmas 1 and 2.
--
--   **Formalization Note** The paper asks for the weak limit "if it exists"; the statement asserts that it exists and identifies it. Since the limit has a density, convergence of the distribution functions at every $x$ is weak convergence. The distribution function of $q_N(\infty)$ is written as $\sum_k \pi^{(N)}_k\mathbf 1\{(k-N)/\sqrt N\le x\}$. The printed density on p. 225 drops a parenthesis in its $x\le0$ line; the corrected density (`ErlangA.Staffing.limitDensity`) is used.
-- source:
--   Garnett, Mandelbaum & Reiman, Designing a Call Center with Impatient Customers, M&SOM 4(3), 2002, pp. 224–225, Appendix C, proof of Theorem 2*, Part 2, "Lhs" (density f, p. 225)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Erlang
import Definitions.Def_DimCallCenters_Rationalized_delayFn
import Definitions.Def_ErlangA_Staffing_Model
open Filter Topology DimCallCenters.Rationalized

namespace ErlangA.Staffing

/-- **Stationary limit** (App. C, proof of Theorem 2*, Part 2, "Lhs", pp. 224–225). Let `μ > 0`,
`λ_N > 0` and `θ_N > 0` for `N ≥ 1`, with `√N(1 − ρ_N) → β ∈ ℝ` where `ρ_N = λ_N/(Nμ)`, and
`θ_N → θ ∈ (0, ∞)`. Then the distribution functions of `q_N(∞) = (Q_N(∞) − N)/√N` converge at
every `x` to `∫_{−∞}^x f`, `f` the (corrected) density `limitDensity β μ θ`. -/
theorem stationary_limit (μ θ β : ℝ) (lam θN : ℕ → ℝ) (hμ : 0 < μ)
    (hlam : ∀ N : ℕ, 1 ≤ N → 0 < lam N) (hθN : ∀ N : ℕ, 1 ≤ N → 0 < θN N)
    (hθ : 0 < θ) (hθlim : Tendsto θN atTop (𝓝 θ))
    (hβ : Tendsto (fun N : ℕ => Real.sqrt N * (1 - lam N / ((N : ℝ) * μ))) atTop (𝓝 β))
    (x : ℝ) :
    Tendsto (fun N : ℕ => ∑' k : ℕ,
        if ((k : ℝ) - N) / Real.sqrt N ≤ x then ErlangA.Abandonment.stationaryDist N (lam N) μ (θN N) k else 0)
      atTop (𝓝 (∫ t in Set.Iic x, limitDensity β μ θ t)) := by sorry

end ErlangA.Staffing
