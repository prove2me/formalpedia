-- Prove2me | Theorems.Thm_DivideChooseBayes_lemma_3_5
-- name    : DivideChooseBayes.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:31:04.75974+00:00
-- url     : https://prove2.me/theorems/42d7fd7e-b1ae-444b-862c-bcdca190224a
-- title:
--   Lemma 3.5 — Algorithm 1 is within an additive $\gamma$ of the optimal divider utility
-- statement:
--   Let the chooser's values be independent with $g^C_i\sim\mathcal N(\mu_i,\sigma_i^2)$, $\sigma_i>0$, let the divider's values $g^D$ be not all zero, and let $\gamma>0$. Run Algorithm 1, with any choice of optimal solutions of the programs $\mathcal C_{P_k}$ on its iterations. Its output $p$ is a division, $p\in[0,1]^n$, and
--
--   $$\mathbb E[u^D(p)]\ \ge\ \mathbb E[u^D(q')]-\gamma\qquad\text{for every division } q',$$
--
--   so the output is within an additive $\gamma$ of the optimal divider utility.
--
--   Differences from the source:
--   - encoding: within an additive γ of the optimal divider utility u* → U(q') − γ ≤ U(output) for every division q'; reason: equivalent, since the optimum is attained (Lemma 3.2); avoids a real supremum
--   - encoding: line 5 takes an optimal solution of C_P → for every selection sol with sol k optimal for C_{P_k} on every iteration k run; reason: the output depends on which optimum is taken; the claim holds for each choice
--   - encoding: Algorithm 1's inputs: divider values not all zero, standard deviations σᵢ > 0, an additive error bound γ → hypotheses gᴰ ≠ 0, σᵢ > 0, γ > 0; reason: the algorithm's own input conditions; γ ≤ 0 or gᴰ = 0 leaves δ ≤ 0 and the while loop does not terminate
--   - encoding: E[uᴰ] of the returned division p → the interim utility at qOfP p = 2p − 1; reason: the same division in the auxiliary variables (Eqs. (1)–(2)); utilities are defined on q
-- source:
--   Tucker-Foltz & Zeckhauser, Playing Divide-and-Choose Given Uncertain Preferences, arXiv:2207.03076v2, Lemma 3.5, p.10 (proof: Appendix C, pp.31–33)

import Mathlib
import Definitions.Def_DivideChooseBayes_qOfP
import Definitions.Def_DivideChooseBayes_IsDivision
import Definitions.Def_DivideChooseBayes_normalPrior
import Definitions.Def_DivideChooseBayes_interimUtility
import Definitions.Def_DivideChooseBayes_IsCPOptimal
import Definitions.Def_DivideChooseBayes_algOutput

open MeasureTheory ProbabilityTheory

namespace DivideChooseBayes

/-- **Lemma 3.5 (additive guarantee of Algorithm 1).**
Tucker-Foltz & Zeckhauser, *Playing Divide-and-Choose Given Uncertain Preferences*,
arXiv:2207.03076v2, Lemma 3.5, p.10: "Algorithm 1 finds a division yielding divider utility within an
additive γ of the optimal divider utility."

Under independent normal priors with `σᵢ > 0`, for `gᴰ` not all zero and `γ > 0`, and for every
selection `sol` of optimal solutions of the programs `C_{P_k}` on the iterations run, the output
`p` of Algorithm 1 is a division (`p ∈ [0,1]ⁿ`), and its interim expected utility is at least
`U(q') − γ` for every division `q'`.

**Formalization Note.** The output `p` is evaluated through its auxiliary variables
`q = 2p − 1` (Eq. (1)). "Within an additive γ of the optimal divider utility" is stated against
every division `q'`, which is equivalent because the optimum is attained (Lemma 3.2). -/
theorem lemma_3_5 {ι : Type*} [Fintype ι] (gD m σ : ι → ℝ) (hgD : ∃ i, gD i ≠ 0)
    (hσ : ∀ i, 0 < σ i) (γ : ℝ) (hγ : 0 < γ) (sol : ℕ → ι → ℝ)
    (hsol : ∀ k < iterationCount gD γ, IsCPOptimal gD m σ (algP gD γ k) (sol k)) :
    (∀ i, algOutput gD γ sol i ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ q' : ι → ℝ, IsDivision q' →
        interimUtility (normalPrior m σ) gD q' - γ ≤
          interimUtility (normalPrior m σ) gD (qOfP (algOutput gD γ sol)) := by sorry

end DivideChooseBayes
