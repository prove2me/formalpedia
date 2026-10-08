-- Prove2me | Theorems.Thm_CappeKLUCB_ExpFam_expected_draws_split
-- name    : CappeKLUCB.ExpFam.expected_draws_split
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T07:19:54.061993+00:00
-- url     : https://prove2.me/theorems/2666341b-ba21-4e39-88e7-3eb1d0cd8daa
-- title:
--   Bound after (7), p. 9 — 𝔼[Nₐ(T)] ≤ 1 + Σ ℙ{μ† ≥ U_{a⋆}(t)} + Σ ℙ{μ† < Uₐ(t), A_{t+1} = a}
-- statement:
--   Let $K\ge2$ arms belong to a canonical regular exponential family $\mathcal D$ indexed by its natural parameter space: the rewards of arm $b$ are i.i.d. with law $\nu_{\theta_b}$, $\theta_b\in\Theta$, independent across arms, with means $\mu_b$; let $\mu^\star = \max_b \mu_b$ and let $a^\star$ be an optimal arm. Let $(A_t)$ be a run of Algorithm 2 with $f = f_1$, with measurable arm choices, $U_b(t)$ the kl-UCB indices and $N_a(T)$ the number of pulls of arm $a$ in rounds $1,\dots,T$. Then for every arm $a$, every $\mu^\dagger\in\mathbb R$ and every horizon $T$,
--   $$\mathbb E[N_a(T)] \le 1 + \sum_{t=K}^{T-1}\mathbb P\{\mu^\dagger \ge U_{a^\star}(t)\} + \sum_{t=K}^{T-1}\mathbb P\{\mu^\dagger < U_a(t)\text{ and } A_{t+1}=a\}.$$
--   On p. 9 the event $\{\mu^\dagger < U_a(t)\}$ is written $\{\hat\nu_{a,N_a(t)}\in\mathcal C_{\mu^\dagger, f(t)/N_a(t)}\}$; in this model it is the event that the kl-UCB index of arm $a$ exceeds $\mu^\dagger$.
--
--   The bound splits the expected number of draws of an arm into a term where the optimal arm is underestimated and a term where arm $a$ is overestimated; the two sums are handled separately in the rest of the analysis.
--
--   **Formalization Note** Probabilities of events defined through the index are written with `P.real` (the outer measure), so no measurability of the index is assumed. The sums are over $t\in\{K,\dots,T-1\}$ (`Finset.Ico K T`), empty when $T\le K$.
-- source:
--   Cappé, Garivier, Maillard, Munos, Stoltz, Kullback–Leibler upper confidence bounds for optimal sequential allocation, arXiv:1210.1136v4, p. 9, display after (7)

import Mathlib
import Definitions.Def_CappeKLUCB_ExpFam_Setting

namespace CappeKLUCB.ExpFam

open MeasureTheory ProbabilityTheory ImprovedLinBandits.UCBDelta RegretBandits.Stochastic
  OptimalBAI.OptProportions

/-- The bound after (7), Cappé et al., arXiv:1210.1136v4, p. 9. -/
theorem expected_draws_split {K : ℕ} (hK : 2 ≤ K) (F : ExpFamily) (hnat : IsNatural F)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (hX : IsStochasticBandit P X μ)
    (θ : Fin K → ℝ) (hθ : ∀ a, θ a ∈ F.Θ) (hlaw : ∀ a, P.map (X a 0) = F.arm (θ a))
    (I : ℕ → Ω → Fin K) (hI : ∀ t, Measurable (I t))
    (hrun : IsKLUCBRun F f₁ X I) (a astar : Fin K) (hastar : μ astar = bestMean μ)
    (μdag : ℝ) (T : ℕ) :
    ∫ ω, (pullCount I a T ω : ℝ) ∂P ≤
      1 + ∑ t ∈ Finset.Ico K T, P.real {ω | klucbIndex F f₁ X I astar t ω ≤ μdag}
        + ∑ t ∈ Finset.Ico K T,
            P.real {ω | μdag < klucbIndex F f₁ X I a t ω ∧ I (t + 1) ω = a} := by sorry

end CappeKLUCB.ExpFam
