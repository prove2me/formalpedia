-- Prove2me | Theorems.Thm_DivideChooseBayes_lemma_3_2
-- name    : DivideChooseBayes.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:31:57.976822+00:00
-- url     : https://prove2.me/theorems/b439017e-fc43-4286-b375-cbe9f2e1a0ef
-- title:
--   Lemma 3.2 (corrected: strict inequality in (4)) — an optimal division with (3) and (4) exists
-- statement:
--   Let $\mu$ be a prior on the chooser's values and $g^D$ the divider's values.
--
--   1. There is a divider-optimal division $q$ with
--   $$\sum_{i=1}^n q_i g^D_i\ \ge\ 0 \qquad\text{and}\qquad \Pr_{g^C\sim\mu}\Big[\sum_{i=1}^n q_i g^C_i>0\Big]\ \le\ \frac12 .$$
--   2. Some division gives the divider an interim expected utility strictly above $\frac12\sum_i g^D_i$ if and only if some division $q$ has
--   $$\sum_{i=1}^n q_i g^D_i > 0 \qquad\text{and}\qquad \Pr_{g^C\sim\mu}\Big[\sum_{i=1}^n q_i g^C_i>0\Big] < \frac12 .$$
--
--   The first condition says the divider weakly prefers pile 1, the second that the chooser is weakly more likely to pick pile 2.
--
--   Differences from the source:
--   - correction: (4) P := Pr[Σᵢ qᵢgᶜᵢ ≥ 0] ≤ 1/2, and the iff with (3), (4) made strict → Pr[Σᵢ qᵢgᶜᵢ > 0] ≤ 1/2, and Pr[Σᵢ qᵢgᶜᵢ > 0] < 1/2 in the iff; reason: the printed existence claim is false: n = 1, gᴰ₁ = 1, prior N(1,1); every q₁ ≠ 0 gives utility < 1/2 = U(0), so q = 0 is the unique optimum and Pr[0 ≥ 0] = 1 > 1/2. The strict event is the probability that the chooser picks pile 1 when (3) holds, and the paper's own P in the proofs of Proposition 3.3 and Lemma 4.2
--   - generalization: the conditional prior of the paper's model (independent across goods) → any probability measure μ on ℝⁿ for the chooser's values, at fixed gᴰ; reason: the statement uses only that μ is a probability measure; the paper's priors are instances
-- source:
--   Tucker-Foltz & Zeckhauser, Playing Divide-and-Choose Given Uncertain Preferences, arXiv:2207.03076v2, Lemma 3.2, p.6 (proof: Appendix B, p.31)

import Mathlib
import Definitions.Def_DivideChooseBayes_IsOptimalDivision

open MeasureTheory ProbabilityTheory

namespace DivideChooseBayes

/-- **Lemma 3.2 (corrected: strict inequality in (4)).**
Tucker-Foltz & Zeckhauser, *Playing Divide-and-Choose Given Uncertain Preferences*,
arXiv:2207.03076v2, Lemma 3.2, p.6: "A divider-optimal division with the following two properties always
exists. • The divider weakly prefers pile 1: ∑ᵢ qᵢgᴰᵢ ≥ 0. (3) • The chooser is weakly more likely
to pick pile 2: P := Pr_{gᶜ∼Ḡᶜ}[∑ᵢ qᵢgᶜᵢ ≥ 0] ≤ 1/2. (4) Furthermore, the divider can achieve a
strictly higher interim expected utility than his proportionality guarantee if and only if both
of these inequalities can be made strict."

For every prior `μ`:
1. there is a divider-optimal division `q` with `∑ᵢ qᵢgᴰᵢ ≥ 0` and `Pr[∑ᵢ qᵢgᶜᵢ > 0] ≤ 1/2`;
2. some division gives interim expected utility `> ½ ∑ᵢ gᴰᵢ` iff some division has
   `∑ᵢ qᵢgᴰᵢ > 0` and `Pr[∑ᵢ qᵢgᶜᵢ > 0] < 1/2`.

**Formalization Note.** (Correction.) The printed event `∑ᵢ qᵢgᶜᵢ ≥ 0` in (4) makes the
existence claim false: for `n = 1`, `gᴰ₁ = 1`, prior `N(1,1)`, the unique optimal division is
`q₁ = 0`, where `Pr[0 ≥ 0] = 1 > 1/2`. The strict event `> 0` is the paper's own `P` in the proofs of
Proposition 3.3 and Lemma 4.2, and the probability that the chooser picks pile 1 when (3) holds.
Stated for every probability measure `μ`. -/
theorem lemma_3_2 {ι : Type*} [Fintype ι] (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    (gD : ι → ℝ) :
    (∃ q : ι → ℝ, IsOptimalDivision μ gD q ∧ 0 ≤ ∑ i, q i * gD i ∧
        μ.real {gC | 0 < ∑ i, q i * gC i} ≤ 1 / 2) ∧
      ((∃ q : ι → ℝ, IsDivision q ∧ 1 / 2 * ∑ i, gD i < interimUtility μ gD q) ↔
        ∃ q : ι → ℝ, IsDivision q ∧ 0 < ∑ i, q i * gD i ∧
          μ.real {gC | 0 < ∑ i, q i * gC i} < 1 / 2) := by sorry

end DivideChooseBayes
