-- Prove2me | Theorems.Thm_BayesBAI_lemma_3
-- name    : BayesBAI.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:58:23.729373+00:00
-- url     : https://prove2.me/theorems/f41bc804-e439-46f0-b2dc-47974a1fe388
-- title:
--   Lemma 3 — three or more candidates contribute $o(1/T)$
-- statement:
--   Under Assumption 1, for every tie-break rule,
--   $$
--   \mathbb E_{\mu\sim H}\Big[\mathbb E_\mu\big[\mathbf 1[\mathcal S,\,|\hat{\mathcal J}^*|\ge3]\,\Delta_{J(T)}\big]\Big]=o\Big(\frac1T\Big).
--   $$
--   Here $\mathbf 1[\mathcal A]=1$ if $\mathcal A$ holds and $0$ otherwise. The decay is uniform in the rule. For $K=2$ the event is empty.
--
--   This disposes of the event that three arms have nearly equal means, which leaves the two-candidate term of Lemma 4.
--
--   Differences from the source:
--   - encoding: conditional cumulative density functions of μ_i and (μ_i, μ_j) with continuous derivatives h_i, h_ij → RegularPrior: jointly measurable h, hh that disintegrate H over the laws H_\i, H_\ij by lintegral, with (4) on [0,1] and δ uniform in the conditioning vector; reason: a conditional density is this object, and C_opt does not depend on the version, since a continuous version is unique for H_\i-a.e. ν (paper.md Reading 1)
--   - encoding: Bernoulli rewards drawn adaptively → the reward tape Fin K → Fin T → Bool with independent entries; the first n pulls of an arm are its first n entries; reason: TSE fixes each stage’s pulls in advance of that stage, so the laws agree
--   - encoding: qT/K and (1−q)T/|Ĵ*| pulls, unrounded → n₁ = ⌈qT/K⌉ and n₂(s) = ⌊(T − K n₁)/s⌋; reason: pull counts are integers; the ceiling keeps Lemma 2, and with s = 2 the sample size n has |2n − T′| ≤ K + 3 (proved in a verification file) (Reading 2)
--   - generalization: arg max with ties broken arbitrarily → every TieBreak rule, with T₀ not depending on the rule; reason: specializes to any fixed rule; a randomized rule is a mixture of these (Reading 3)
--   - encoding: any q > 0, K arms → q ∈ (0,1), 2 ≤ K; reason: Algorithm 1 requires q ∈ (0,1), and μ*_\i needs a second arm (Reading 4)
--   - encoding: = o(1/T) → ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, ∀ sel, |…| ≤ ε/T; reason: the definition of o(1/T); K, q, H are fixed
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, Lemma 3, p.7

import Mathlib
import Definitions.Def_BayesBAI_RegularPrior
import Definitions.Def_BayesBAI_recommend
import Definitions.Def_BayesBAI_goodEvent
import Definitions.Def_BayesBAI_tapeExp
import Definitions.Def_BayesBAI_gap

open MeasureTheory

namespace BayesBAI

/-- Lemma 3, Komiyama, Ariu, Kato, Qin, arXiv:2111.09885v3, p.7:
`𝔼_{μ∼H}[𝔼_μ[𝟏[𝒮, |Ĵ*| ≥ 3] Δ_{J(T)}]] = o(1/T)`.

**Formalization Note.** `o(1/T)` is `∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, |⋯| ≤ ε / T`, with `T₀` not depending on
the tie-break rule. For `K = 2` the event is empty. -/
theorem lemma_3 {K : ℕ} (hK : 2 ≤ K) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {H : Measure (Fin K → ℝ)}
    {h : (i : Fin K) → ℝ → ({j : Fin K // j ≠ i} → ℝ) → ℝ}
    {hh : (i j : Fin K) → ℝ → ℝ → ({k : Fin K // k ≠ i ∧ k ≠ j} → ℝ) → ℝ}
    (hH : RegularPrior H h hh) :
    ∀ ε > 0, ∃ T₀ : ℕ, ∀ T ≥ T₀, ∀ sel : TieBreak K,
      |∫ μ, tapeExp μ
          (Set.indicator {ω : Tape K T | goodEvent q μ ω ∧ 3 ≤ (candidates q ω).card}
            (fun ω => gap hK μ (recommend sel q ω))) ∂H| ≤ ε / (T : ℝ) := by sorry

end BayesBAI
