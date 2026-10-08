-- Prove2me | Theorems.Thm_CappeKLUCB_ExpFam_theorem_1
-- name    : CappeKLUCB.ExpFam.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T07:21:15.806984+00:00
-- url     : https://prove2.me/theorems/0c4f0d7e-dec2-4537-8a8a-a266d85570ac
-- title:
--   Theorem 1, p. 14 — kl-UCB with f(t) = log t + 3 log log t draws a suboptimal arm at most log(T)/d(μₐ, μ⋆) + O(√log T) times in expectation
-- statement:
--   Let $\mathcal D = \{\nu_\theta : \theta\in\Theta\}$ be a canonical, regular, one-parameter exponential family indexed by its natural parameter space $\Theta\subseteq\mathbb R$: $\frac{d\nu_\theta}{d\rho}(x) = \exp(x\theta - b(\theta))$, $\Theta = \{\theta : \int e^{x\theta}d\rho(x)<\infty\}$ is an open interval, and $b$ is twice differentiable. Write $I = \dot b(\Theta)$ for the open interval of means and $d$ for the divergence (11), $d(\mu,\mu') = \mathrm{KL}(\nu_{\dot b^{-1}(\mu)},\nu_{\dot b^{-1}(\mu')})$.
--
--   Consider a bandit problem with $K\ge2$ arms, all in $\mathcal D$: the rewards of arm $b$ are i.i.d. with law $\nu_{\theta_b}$ and mean $\mu_b$, independent across arms, and $\mu^\star = \max_b\mu_b$. Run Algorithm 2 (kl-UCB) with the divergence $d$ and
--   $$f(t) = \log t + 3\log\log t\ \ (t\ge3),\qquad f(1)=f(2)=f(3).$$
--   Then for every suboptimal arm $a$ ($\mu_a<\mu^\star$) and every horizon $T\ge3$, the number $N_a(T)$ of draws of arm $a$ in rounds $1,\dots,T$ satisfies
--   $$\mathbb E[N_a(T)] \le \frac{\log T}{d(\mu_a,\mu^\star)} + 2\sqrt{\frac{2\pi\sigma^2_{a,\star}\,(d'(\mu_a,\mu^\star))^2}{(d(\mu_a,\mu^\star))^3}}\sqrt{\log T + 3\log\log T} + \Bigl(4e + \frac{3}{d(\mu_a,\mu^\star)}\Bigr)\log\log T + 8\sigma^2_{a,\star}\Bigl(\frac{d'(\mu_a,\mu^\star)}{d(\mu_a,\mu^\star)}\Bigr)^2 + 6,$$
--   where $\sigma^2_{a,\star} = \max\{\mathrm{Var}(\nu_\theta) : \mu_a\le\mathrm E(\nu_\theta)\le\mu^\star\}$ and $d'(\cdot,\mu^\star)$ is the derivative of $d(\cdot,\mu^\star)$.
--
--   The leading term $\log T/d(\mu_a,\mu^\star)$ matches the Lai–Robbins lower bound, so kl-UCB is asymptotically optimal in every such family, and the bound is explicit for every finite horizon.
--
--   **Formalization Note** The rewards are a stack $X_{b,k}$ (the $(k+1)$-st reward of arm $b$), mutually independent and identically distributed per arm (the paper's §2.2 representation), with $\mathrm{law}(X_{b,0}) = \nu_{\theta_b}$; arms are `Fin K`. The family structure carries $\ddot b>0$ on $\Theta$ (strict convexity, which the page derives). The arm choices are required measurable (so $N_a(T)$ is a random variable) and non-anticipating (each $A_{t+1}$ a measurable function of the arms and rewards observed so far, the paper's "based on the information gained in the past", p. 5); ties in the argmax may be broken by any such rule. The supremum defining $\sigma^2_{a,\star}$ is over the parameters $\theta\in\Theta$ with $\mu_a\le\dot b(\theta)\le\mu^\star$; it is a maximum.
-- source:
--   Cappé, Garivier, Maillard, Munos, Stoltz, Kullback–Leibler upper confidence bounds for optimal sequential allocation, arXiv:1210.1136v4, p. 14, Theorem 1

import Mathlib
import Definitions.Def_CappeKLUCB_ExpFam_Setting

namespace CappeKLUCB.ExpFam

open MeasureTheory ProbabilityTheory ImprovedLinBandits.UCBDelta RegretBandits.Stochastic
  OptimalBAI.OptProportions

/-- Theorem 1, Cappé et al., arXiv:1210.1136v4, p. 14. -/
theorem theorem_1 {K : ℕ} (hK : 2 ≤ K) (F : ExpFamily) (hnat : IsNatural F)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (hX : IsStochasticBandit P X μ)
    (θ : Fin K → ℝ) (hθ : ∀ a, θ a ∈ F.Θ) (hlaw : ∀ a, P.map (X a 0) = F.arm (θ a))
    (I : ℕ → Ω → Fin K) (hI : ∀ t, Measurable (I t))
    (hadapt : IsNonanticipating X I) (hrun : IsKLUCBRun F f₁ X I)
    (a : Fin K) (ha : μ a < bestMean μ) (T : ℕ) (hT : 3 ≤ T) :
    ∫ ω, (pullCount I a T ω : ℝ) ∂P ≤
      Real.log T / F.d (μ a) (bestMean μ)
        + 2 * Real.sqrt (2 * Real.pi * varBound F (μ a) (bestMean μ)
            * (deriv (fun m => F.d m (bestMean μ)) (μ a)) ^ 2
            / (F.d (μ a) (bestMean μ)) ^ 3)
          * Real.sqrt (Real.log T + 3 * Real.log (Real.log T))
        + (4 * Real.exp 1 + 3 / F.d (μ a) (bestMean μ)) * Real.log (Real.log T)
        + 8 * varBound F (μ a) (bestMean μ)
            * (deriv (fun m => F.d m (bestMean μ)) (μ a) / F.d (μ a) (bestMean μ)) ^ 2
        + 6 := by sorry

end CappeKLUCB.ExpFam
