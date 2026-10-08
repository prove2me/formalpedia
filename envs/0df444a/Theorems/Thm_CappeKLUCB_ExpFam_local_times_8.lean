-- Prove2me | Theorems.Thm_CappeKLUCB_ExpFam_local_times_8
-- name    : CappeKLUCB.ExpFam.local_times_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T07:20:19.585675+00:00
-- url     : https://prove2.me/theorems/b3eb74cc-71f3-4025-aad6-194b8d767669
-- title:
--   (8), pp. 9–10 — passing to local times: Σₜ ℙ{μ† < Uₐ(t), A_{t+1} = a} ≤ Σ_{n=1}^{T−K} ℙ{ν̂_{a,n} ∈ 𝒞_{μ†, f(T)/n}}
-- statement:
--   In the setting of Theorem 1 (arms in a canonical regular exponential family indexed by its natural parameter space, a run of Algorithm 2 with $f = f_1$ and measurable arm choices), let $a$ be an arm, $\mu^\dagger\in\mathbb R$ and $T\ge K$. Write $\hat\mu_{a,n} = \frac1n\sum_{k=1}^n X_{a,k}$ for the mean of the first $n$ rewards of arm $a$ and $\mathrm{klIndex}(m,\gamma) = \sup\{\mu\in\bar I : d(m,\mu)\le\gamma\}$. Then
--   $$\sum_{t=K}^{T-1}\mathbb P\{\mu^\dagger < U_a(t)\text{ and } A_{t+1}=a\} \le \sum_{n=1}^{T-K}\mathbb P\bigl\{\mu^\dagger < \mathrm{klIndex}(\hat\mu_{a,n}, f(T)/n)\bigr\}.$$
--   The right-hand event is the paper's $\{\hat\nu_{a,n}\in\mathcal C_{\mu^\dagger, f(T)/n}\}$.
--
--   The right-hand side no longer refers to the algorithm: it only involves the i.i.d. rewards of arm $a$ at fixed sample sizes $n$. This is the step that removes the random number of summands from the leading term.
--
--   **Formalization Note** Probabilities of index events are outer measures (`P.real`).
-- source:
--   Cappé, Garivier, Maillard, Munos, Stoltz, Kullback–Leibler upper confidence bounds for optimal sequential allocation, arXiv:1210.1136v4, pp. 9–10, (8)

import Mathlib
import Definitions.Def_CappeKLUCB_ExpFam_Setting

namespace CappeKLUCB.ExpFam

open MeasureTheory ProbabilityTheory ImprovedLinBandits.UCBDelta RegretBandits.Stochastic
  OptimalBAI.OptProportions

/-- (8), Cappé et al., arXiv:1210.1136v4, pp. 9–10. -/
theorem local_times_8 {K : ℕ} (hK : 2 ≤ K) (F : ExpFamily) (hnat : IsNatural F)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (hX : IsStochasticBandit P X μ)
    (θ : Fin K → ℝ) (hθ : ∀ a, θ a ∈ F.Θ) (hlaw : ∀ a, P.map (X a 0) = F.arm (θ a))
    (I : ℕ → Ω → Fin K) (hI : ∀ t, Measurable (I t))
    (hrun : IsKLUCBRun F f₁ X I) (a : Fin K) (μdag : ℝ) (T : ℕ) (hT : K ≤ T) :
    ∑ t ∈ Finset.Ico K T, P.real {ω | μdag < klucbIndex F f₁ X I a t ω ∧ I (t + 1) ω = a} ≤
      ∑ n ∈ Finset.Icc 1 (T - K),
        P.real {ω | μdag < klIndex F (sampleMean X a n ω) (f₁ T / (n : ℝ))} := by sorry

end CappeKLUCB.ExpFam
