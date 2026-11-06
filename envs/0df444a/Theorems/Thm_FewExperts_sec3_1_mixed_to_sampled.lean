-- Prove2me | Theorems.Thm_FewExperts_sec3_1_mixed_to_sampled
-- name    : FewExperts.sec3_1_mixed_to_sampled
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:53:13.915557+00:00
-- url     : https://prove2.me/theorems/8006428c-32bc-4528-ba0c-3f7949722ad3
-- title:
--   §3.1, p.13 — the sampled gain is within $\sqrt{T\ln(2/\delta)/2}$ of the mixed gain w.p. $1-\delta$
-- statement:
--   Let $(\mathcal F_t)$ be a filtration on a probability space. Suppose that at each round $t=1,\dots,T$ an algorithm predicts a mixture $M_t$ over the $N$ experts that is $\mathcal F_{t-1}$-measurable. It plays the expert $I_t$ drawn from $M_t$ by the inverse-CDF device, using a uniform variable $U_t$ that is $\mathcal F_t$-measurable and independent of $\mathcal F_{t-1}$. Then for every gain array with values in $[0,1]$ and every $\delta\in(0,1)$,
--
--   $$
--   \Pr\Bigl[\Bigl|\sum_{t=1}^T g_t^{I_t}-\sum_{t=1}^T\sum_i M_t(i)\,g_t^i\Bigr|>\sqrt{\tfrac{T\ln(2/\delta)}{2}}\Bigr]\le\delta .
--   $$
--
--   This lets the regret of the sampled play be bounded by that of the mixed predictions.
--
--   Differences from the source:
--   - reading: the actual gain differs from its expectation under the chosen mixtures by at most O(√(T log T)) with high probability → for every δ ∈ (0, 1), the deviation exceeds √(T ln(2/δ)/2) with probability at most δ; reason: the explicit form of the O and of "with high probability"; δ = 1/T gives O(√(T log T))
--   - generalization: algorithms that predict a mix of experts and sample from it → any mixtures that are predictable for a filtration, sampled with fresh independent uniform variables through sampleFin; reason: the algorithm of Theorem 4 is such an algorithm: its mixtures never read the play variables
--   - encoding: Pr[bad event] ≤ β → the (outer) measure of the bad event is ≤ ENNReal.ofReal β; reason: equal for measurable events; no measurability statement is needed
-- source:
--   Asi, Feldman, Kale, Koren, Singhal, Talwar, A Few Experts Suffice: Near-Optimal (Private) Online Learning with Limited Subscriptions (manuscript, STOC 2027 submission, sha256 6f26c545886ca169ae416f4056c22bc260e33c3a4fc5d5d8cabe21b5d45398ee), §3.1, p.13 (PDF p.14)

import Mathlib
import Definitions.Def_FewExperts_gainRegret
import Definitions.Def_FewExperts_sampleFin

namespace FewExperts

open MeasureTheory ProbabilityTheory

/-- **§3.1: the realized gain tracks the mixed gain.**
Asi, Feldman, Kale, Koren, Singhal, Talwar, *A Few Experts Suffice* (manuscript, sha256
6f26c545…), §3.1, p.13 (PDF 14): "Throughout, we allow algorithms to predict a mix of
(subscribed) experts … For high-probability bounds, the actual gain differs from its expectation
under the chosen mixtures by at most O(√(T log T)) with high probability, by Azuma–Hoeffding
(Lemma 1)."

On a probability space `(Ω, P)` with a filtration `ℱ`, let `M t` (`t = 1, …, T`) be mixtures over
the `N` experts that are `ℱ_{t−1}`-measurable, and let the expert played at round `t` be
`I_t = sampleFin (M t) (U t)`, where `U t` is uniform on `[0, 1]`, `ℱ_t`-measurable and
independent of `ℱ_{t−1}`. Then for every gain array with values in `[0, 1]` and every
`δ ∈ (0, 1)`, with probability at least `1 − δ` the realized gain `∑_{t ≤ T} g_t^{I_t}` and the
mixed gain `∑_{t ≤ T} ∑_i M_t(i) g_t^i` differ by at most `√(T ln(2/δ)/2)`.

**Formalization Note** The paper's "O(√(T log T)) with high probability" is made explicit: the
deviation is `√(T ln(2/δ)/2)` with failure probability `δ` (taking `δ = 1/T` gives
`O(√(T log T))`). The mixtures may depend on everything that happened before round `t`; the
sampling device is `sampleFin`, as in the algorithm of Theorem 4. -/
theorem sec3_1_mixed_to_sampled {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ) (N : ℕ) [NeZero N] (T : ℕ)
    (g : ℕ → Fin N → ℝ) (hg : IsGainSeq T g)
    (M : ℕ → Ω → Fin N → ℝ) (U : ℕ → Ω → unitInterval)
    (hMmeas : ∀ t, 1 ≤ t → t ≤ T → Measurable[ℱ (t - 1)] (M t))
    (hMprob : ∀ t, 1 ≤ t → t ≤ T → ∀ ω, IsProbVec (M t ω))
    (hUmeas : ∀ t, 1 ≤ t → t ≤ T → Measurable[ℱ t] (U t))
    (hUind : ∀ t, 1 ≤ t → t ≤ T →
      Indep (MeasurableSpace.comap (U t) inferInstance) (ℱ (t - 1)) P)
    (hUlaw : ∀ t, 1 ≤ t → t ≤ T → P.map (U t) = volume)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    P {ω | Real.sqrt (T * Real.log (2 / δ) / 2) <
        |∑ t ∈ Finset.Icc 1 T, g t (sampleFin (M t ω) (U t ω)) -
          ∑ t ∈ Finset.Icc 1 T, ∑ i, M t ω i * g t i|} ≤ ENNReal.ofReal δ := by sorry

end FewExperts
