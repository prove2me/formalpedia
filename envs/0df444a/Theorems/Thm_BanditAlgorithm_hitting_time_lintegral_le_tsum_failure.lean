-- Prove2me | Theorems.Thm_BanditAlgorithm_hitting_time_lintegral_le_tsum_failure
-- name    : BanditAlgorithm.hitting_time_lintegral_le_tsum_failure
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T23:16:57.284595+00:00
-- url     : https://prove2.me/theorems/0816d636-3760-4725-afa6-66f7fc2c0be0
-- title:
--   Mean of a hitting time is bounded by the sum of failure probabilities
-- statement:
--   Let $G_0,G_1,\dots$ be measurable events and let
--   $$T(\omega)=\inf\{N\in\mathbb N:\ \omega\in G_n\text{ for every }n\ge N\}$$
--   be the first index from which $\omega$ belongs to all of them (with the value $0$ when no such index exists). Then
--   $$\int T\,d\mu\ \le\ \sum_{m=0}^{\infty}(m+1)\,\mu(G_m^{c}).$$
--
--   So $T$ is integrable as soon as the failure probabilities $\mu(G_m^c)$ are summable against the index $m$, which is what any geometric or polynomial-of-degree-below-$-2$ concentration bound supplies. This is the layer-cake estimate $\mathbb E[T]=\sum_n\mu(T>n)$ combined with $\{T>n\}\subseteq\bigcup_{m\ge n}G_m^{c}$, and it is stated with no measurability assumption on $T$ itself: the bound is proved pointwise, $T(\omega)\le\sum_m(m+1)\mathbf 1_{G_m^c}(\omega)$, and monotonicity of the lower integral needs nothing of the smaller function.
--
--   The estimate is sharp in the only case that matters: if $\omega$ fails the events exactly on a finite set with largest element $m_0$, then $T(\omega)=m_0+1$ and the $m_0$-th summand alone already contributes $m_0+1$.
-- source:
--   Standard first-moment (layer-cake) estimate for the last failure time of a sequence of events; used here to supply the integrable random time in Garivier & Kaufmann, Optimal Best Arm Identification with Fixed Confidence, COLT 2016, Proposition 13.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Analysis.SpecificLimits.Normed

open MeasureTheory ENNReal NNReal

theorem BanditAlgorithm.hitting_time_lintegral_le_tsum_failure {α : Type*}
    [MeasurableSpace α] (G : ℕ → Set α) (hG : ∀ m, MeasurableSet (G m))
    (μ : MeasureTheory.Measure α) :
    ∫⁻ ω, ((sInf {N : ℕ | ∀ n, N ≤ n → ω ∈ G n} : ℕ) : ℝ≥0∞) ∂μ
      ≤ ∑' m : ℕ, ((m : ℝ≥0∞) + 1) * μ (G m)ᶜ := by
  sorry
