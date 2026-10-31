-- Prove2me | Theorems.Thm_DivideChooseBayes_lemma_3_1
-- name    : DivideChooseBayes.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:32:23.584985+00:00
-- url     : https://prove2.me/theorems/4b8cb2af-7657-4883-9198-57cb6765a0d6
-- title:
--   Lemma 3.1 — proportionality for the chooser, expected proportionality for the divider
-- statement:
--   Let $\mu$ be a prior (a probability measure on the chooser's values $g^C\in\mathbb R^n$, conditioned on the divider's fixed values $g^D$). The chooser picks her higher-valued pile, breaking ties in favour of the divider.
--
--   1. For every division $q\in[-1,1]^n$ and every realization $g^C$, the chooser's payoff satisfies
--   $$u^C\ \ge\ \frac12\sum_{i=1}^n g^C_i .$$
--   2. For every divider-optimal division $q$,
--   $$\mathbb E_{g^C\sim\mu}[u^D]\ \ge\ \frac12\sum_{i=1}^n g^D_i .$$
--
--   The two right-hand sides are the **proportionality guarantees** of the chooser and the divider.
--
--   Differences from the source:
--   - generalization: (i) holds in any equilibrium → (i) holds for every division q; reason: an equilibrium division is a division
--   - generalization: equilibrium: subgame-perfect Bayes-Nash with the divider's own tie-breaking → (ii) for every divider-optimal division at the interim stage, the chooser following her higher pile with ties to the divider; reason: every equilibrium division is optimal at the interim stage (p.6, footnote 2); the Lean does not require the divider's tie-break among optima
--   - generalization: the conditional prior of the paper's model (independent across goods) → any probability measure μ on ℝⁿ for the chooser's values, at fixed gᴰ; reason: the statement uses only that μ is a probability measure; the paper's priors are instances
-- source:
--   Tucker-Foltz & Zeckhauser, Playing Divide-and-Choose Given Uncertain Preferences, arXiv:2207.03076v2, Lemma 3.1, p.6 (proof: Appendix A, p.30)

import Mathlib
import Definitions.Def_DivideChooseBayes_chooserUtility
import Definitions.Def_DivideChooseBayes_IsOptimalDivision

open MeasureTheory ProbabilityTheory

namespace DivideChooseBayes

/-- **Lemma 3.1 (proportionality for the chooser, expected proportionality for the divider).**
Tucker-Foltz & Zeckhauser, *Playing Divide-and-Choose Given Uncertain Preferences*,
arXiv:2207.03076v2, Lemma 3.1, p.6: "In any equilibrium of the divide-and-choose game, the following hold.
(i) For any realizations of gᴰ and gᶜ, uᶜ ≥ ½ ∑ᵢ gᶜᵢ. (ii) For any realization of gᴰ,
E_{gᶜ∼Ḡᶜ}[uᴰ] ≥ ½ ∑ᵢ gᴰᵢ."

For every prior `μ` (a probability measure on the chooser's values, conditioned on the fixed `gᴰ`):
(i) for every division `q` and every `gᶜ`, the chooser's payoff is at least `½ ∑ᵢ gᶜᵢ`;
(ii) every divider-optimal division gives the divider interim expected utility at least
`½ ∑ᵢ gᴰᵢ`.

**Formalization Note.** An equilibrium at the interim stage is: the chooser picks her
higher-valued pile with ties broken for the divider (`ChoosesPileOne`), and the divider plays an
optimal division. (i) is stated for every division, (ii) for every optimal division, and both for
every prior, including correlated values across goods. -/
theorem lemma_3_1 {ι : Type*} [Fintype ι] (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    (gD : ι → ℝ) :
    (∀ q : ι → ℝ, IsDivision q → ∀ gC : ι → ℝ, 1 / 2 * ∑ i, gC i ≤ chooserUtility gD q gC) ∧
      ∀ q : ι → ℝ, IsOptimalDivision μ gD q → 1 / 2 * ∑ i, gD i ≤ interimUtility μ gD q := by sorry

end DivideChooseBayes
