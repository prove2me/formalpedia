-- Prove2me | Theorems.Thm_DivideChooseBayes_eq_10
-- name    : DivideChooseBayes.eq_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:31:10.559742+00:00
-- url     : https://prove2.me/theorems/f3bb1316-c488-4c29-a3b2-73161963d87d
-- title:
--   Eq. (10) — $\mathbb E[u^D] = \sum_i g^D_i/2 + (1/2 - P)\sum_i q_i g^D_i$
-- statement:
--   Let $\mu$ be a prior on the chooser's values and $g^D$ the divider's values. For every division $q\in[-1,1]^n$, with $P$ the probability that the chooser picks pile 1,
--
--   $$\mathbb E[u^D]=\sum_{i=1}^n\frac{g^D_i}{2}+\Big(\frac12-P\Big)\sum_{i=1}^n q_i g^D_i .$$
--
--   The identity separates the divider's proportionality guarantee from a gain term, which is positive exactly when he prefers pile 1 and the chooser takes it with probability below $1/2$, or the reverse.
--
--   Differences from the source:
--   - generalization: the conditional prior of the paper's model (independent across goods) → any probability measure μ on ℝⁿ for the chooser's values, at fixed gᴰ; reason: the statement uses only that μ is a probability measure; the paper's priors are instances
-- source:
--   Tucker-Foltz & Zeckhauser, Playing Divide-and-Choose Given Uncertain Preferences, arXiv:2207.03076v2, Appendix B, p.31, Eq. (10)

import Mathlib
import Definitions.Def_DivideChooseBayes_IsDivision
import Definitions.Def_DivideChooseBayes_interimUtility
import Definitions.Def_DivideChooseBayes_pileOneProb

open MeasureTheory ProbabilityTheory

namespace DivideChooseBayes

/-- **Eq. (10): the divider's interim expected utility.**
Tucker-Foltz & Zeckhauser, *Playing Divide-and-Choose Given Uncertain Preferences*,
arXiv:2207.03076v2, Appendix B, p.31, Eq. (10):
`E[uᴰ] = ∑ᵢ gᴰᵢ/2 + (1/2 − P) ∑ᵢ qᵢ gᴰᵢ`.

For every prior `μ` and every division `q`, with `P` the probability that the chooser picks pile 1.

**Formalization Note.** Stated for every probability measure `μ`, including correlated values. -/
theorem eq_10 {ι : Type*} [Fintype ι] (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    (gD q : ι → ℝ) (hq : IsDivision q) :
    interimUtility μ gD q = ∑ i, gD i / 2 + (1 / 2 - pileOneProb μ gD q) * ∑ i, q i * gD i := by sorry

end DivideChooseBayes
