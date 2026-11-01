-- Prove2me | Theorems.Thm_BayesBAI_lemma_4
-- name    : BayesBAI.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:58:14.070921+00:00
-- url     : https://prove2.me/theorems/235bbb05-662d-45b3-9d95-4216505d6cca
-- title:
--   Lemma 4 — two candidates contribute at most $C_{\mathrm{opt}}/T'+o(1/T)$
-- statement:
--   Under Assumption 1, for every tie-break rule,
--   $$
--   \mathbb E_{\mu\sim H}\Big[\mathbb E_\mu\big[\mathbf 1[\mathcal S,\,|\hat{\mathcal J}^*|=2]\,\Delta_{J(T)}\big]\Big]\le\frac{C_{\mathrm{opt}}}{T'}+o\Big(\frac1T\Big).
--   $$
--   The $o(1/T)$ is one-sided and uniform in the rule. This is the leading term of the Bayesian simple regret.
--
--   Differences from the source:
--   - encoding: conditional cumulative density functions of μ_i and (μ_i, μ_j) with continuous derivatives h_i, h_ij → RegularPrior: jointly measurable h, hh that disintegrate H over the laws H_\i, H_\ij by lintegral, with (4) on [0,1] and δ uniform in the conditioning vector; reason: a conditional density is this object, and C_opt does not depend on the version, since a continuous version is unique for H_\i-a.e. ν (paper.md Reading 1)
--   - encoding: Bernoulli rewards drawn adaptively → the reward tape Fin K → Fin T → Bool with independent entries; the first n pulls of an arm are its first n entries; reason: TSE fixes each stage’s pulls in advance of that stage, so the laws agree
--   - encoding: qT/K and (1−q)T/|Ĵ*| pulls, unrounded → n₁ = ⌈qT/K⌉ and n₂(s) = ⌊(T − K n₁)/s⌋; reason: pull counts are integers; the ceiling keeps Lemma 2, and with s = 2 the sample size n has |2n − T′| ≤ K + 3 (proved in a verification file) (Reading 2)
--   - generalization: arg max with ties broken arbitrarily → every TieBreak rule, with T₀ not depending on the rule; reason: specializes to any fixed rule; a randomized rule is a mixture of these (Reading 3)
--   - encoding: any q > 0, K arms → q ∈ (0,1), 2 ≤ K; reason: Algorithm 1 requires q ∈ (0,1), and μ*_\i needs a second arm (Reading 4)
--   - encoding: ≤ C_opt/T′ + o(1/T) → ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, ∀ sel, … ≤ … + ε/T; reason: o(1/T) in an upper bound means this (footnote 6, p.9); K, q, H are fixed
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, Lemma 4, p.7

import Mathlib
import Definitions.Def_BayesBAI_RegularPrior
import Definitions.Def_BayesBAI_recommend
import Definitions.Def_BayesBAI_goodEvent
import Definitions.Def_BayesBAI_tapeExp
import Definitions.Def_BayesBAI_gap
import Definitions.Def_BayesBAI_Copt
import Definitions.Def_BayesBAI_tPrime

open MeasureTheory

namespace BayesBAI

/-- Lemma 4, Komiyama, Ariu, Kato, Qin, arXiv:2111.09885v3, p.7:
`𝔼_{μ∼H}[𝔼_μ[𝟏[𝒮, |Ĵ*| = 2] Δ_{J(T)}]] ≤ C_opt/T′ + o(1/T)`.

**Formalization Note.** `o(1/T)` in an upper bound is one-sided (footnote 6): for every `ε > 0` the bound
holds with `ε/T` for all large `T`, with `T₀` not depending on the tie-break rule. -/
theorem lemma_4 {K : ℕ} (hK : 2 ≤ K) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {H : Measure (Fin K → ℝ)}
    {h : (i : Fin K) → ℝ → ({j : Fin K // j ≠ i} → ℝ) → ℝ}
    {hh : (i j : Fin K) → ℝ → ℝ → ({k : Fin K // k ≠ i ∧ k ≠ j} → ℝ) → ℝ}
    (hH : RegularPrior H h hh) :
    ∀ ε > 0, ∃ T₀ : ℕ, ∀ T ≥ T₀, ∀ sel : TieBreak K,
      ∫ μ, tapeExp μ
          (Set.indicator {ω : Tape K T | goodEvent q μ ω ∧ (candidates q ω).card = 2}
            (fun ω => gap hK μ (recommend sel q ω))) ∂H ≤
        Copt hK H h / tPrime K q T + ε / (T : ℝ) := by sorry

end BayesBAI
