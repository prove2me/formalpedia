-- Prove2me | Theorems.Thm_CappeKLUCB_ExpFam_deviation_13
-- name    : CappeKLUCB.ExpFam.deviation_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T07:20:48.549328+00:00
-- url     : https://prove2.me/theorems/4a5702ff-faa1-4fb9-9f9c-655609588135
-- title:
--   (13), p. 14 — ℙ{μ̂_{a⋆}(t) < μ⋆, d(μ̂_{a⋆}(t), μ⋆) ≥ ε/N_{a⋆}(t)} ≤ e⌈ε log t⌉ exp(−ε)
-- statement:
--   In the setting of Theorem 1 (arms in a canonical regular exponential family indexed by its natural parameter space, a run of Algorithm 2 with $f = f_1$ whose arm choices are measurable and non-anticipating), let $a^\star$ be an optimal arm with mean $\mu^\star$, let $N_{a^\star}(t)$ be its number of pulls in rounds $1,\dots,t$ and $\hat\mu_{a^\star}(t)$ the mean of its observed rewards. For every $\varepsilon>1$ and every $t\ge2$,
--   $$\mathbb P\Bigl\{N_{a^\star}(t)\ge1,\ \hat\mu_{a^\star}(t) < \mu^\star\ \text{and}\ d(\hat\mu_{a^\star}(t),\mu^\star) \ge \frac{\varepsilon}{N_{a^\star}(t)}\Bigr\} \le e\,\lceil\varepsilon\log t\rceil\exp(-\varepsilon).$$
--   Here $d(\cdot,\mu^\star)$ is the divergence (11) extended by continuity to the closure $\bar I$ of the mean space, since the empirical mean may be an endpoint of $\bar I$.
--
--   This is a deviation bound for an empirical mean with a random number of summands: up to the factor $e\lceil\varepsilon\log t\rceil$ it matches the Chernoff bound for a fixed sample size. It controls the probability that the optimal arm is underestimated, i.e. the sum $\sum_t \mathbb P\{\mu^\star\ge U_{a^\star}(t)\}$ of (10).
--
--   **Formalization Note** The paper states (13) for all $t\ge1$. At $t=1$ the right-hand side is $e\lceil 0\rceil e^{-\varepsilon} = 0$, while a run that pulls $a^\star$ first makes the left-hand side the positive probability $\mathbb P\{X<\mu^\star,\ d(X,\mu^\star)\ge\varepsilon\}$ of a single reward $X$ (e.g. for Gaussian arms); the statement is therefore made for $t\ge2$. The paper's $\hat\mu_{a^\star}(t)$ is undefined when $N_{a^\star}(t)=0$; the conjunct $N_{a^\star}(t)\ge1$ makes the event meaningful. Non-anticipation (the arm of round $t+1$ is a measurable function of the arms and rewards observed in rounds $1,\dots,t$) is the paper's "based on the information gained in the past" (p. 5); without it a tie-breaking rule could look at future rewards of $a^\star$.
-- source:
--   Cappé, Garivier, Maillard, Munos, Stoltz, Kullback–Leibler upper confidence bounds for optimal sequential allocation, arXiv:1210.1136v4, p. 14, (13)

import Mathlib
import Definitions.Def_CappeKLUCB_ExpFam_Setting

namespace CappeKLUCB.ExpFam

open MeasureTheory ProbabilityTheory ImprovedLinBandits.UCBDelta RegretBandits.Stochastic
  OptimalBAI.OptProportions

/-- (13), Cappé et al., arXiv:1210.1136v4, p. 14. The page says "for all `t ≥ 1`";
at `t = 1` the right-hand side `e ⌈ε log 1⌉ exp(-ε)` is `0` and the claim fails for a run that pulls
`a⋆` first, so the statement is made for `t ≥ 2`. The conjunct `1 ≤ N_{a⋆}(t)` is where `μ̂_{a⋆}(t)`
is defined. -/
theorem deviation_13 {K : ℕ} (hK : 2 ≤ K) (F : ExpFamily) (hnat : IsNatural F)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (hX : IsStochasticBandit P X μ)
    (θ : Fin K → ℝ) (hθ : ∀ a, θ a ∈ F.Θ) (hlaw : ∀ a, P.map (X a 0) = F.arm (θ a))
    (I : ℕ → Ω → Fin K) (hI : ∀ t, Measurable (I t))
    (hadapt : IsNonanticipating X I) (hrun : IsKLUCBRun F f₁ X I)
    (astar : Fin K) (hastar : μ astar = bestMean μ) (ε : ℝ) (hε : 1 < ε) (t : ℕ) (ht : 2 ≤ t) :
    P {ω | 1 ≤ pullCount I astar t ω ∧
        sampleMean X astar (pullCount I astar t ω) ω < bestMean μ ∧
        ENNReal.ofReal (ε / (pullCount I astar t ω : ℝ)) ≤
          dExt F (sampleMean X astar (pullCount I astar t ω) ω) (bestMean μ)} ≤
      ENNReal.ofReal (Real.exp 1 * (⌈ε * Real.log t⌉₊ : ℝ) * Real.exp (-ε)) := by sorry

end CappeKLUCB.ExpFam
