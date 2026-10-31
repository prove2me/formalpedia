-- Prove2me | Theorems.Thm_DivideChooseBayes_appendix_c_grid_feasible
-- name    : DivideChooseBayes.appendix_c_grid_feasible
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:30:15.834409+00:00
-- url     : https://prove2.me/theorems/507f0bbf-5c5a-46c0-9a97-c244ca94f054
-- title:
--   Appendix C, pp.32–33 — some iteration has $P-\delta\le P^*\le P$, and $q^*$ is feasible for $\mathcal C_P$ there
-- statement:
--   Let the chooser's values be independent with $g^C_i\sim\mathcal N(\mu_i,\sigma_i^2)$, $\sigma_i>0$, let the divider's values $g^D$ be not all zero, and let $\gamma>0$, $\delta=\gamma/\sum_i|g^D_i|$ and $P_k=1/2-k\delta$. Let $q^*$ be a division with $\sum_i q^*_i g^D_i\ge 0$ whose probability $P^*$ that the chooser picks pile 1 is at most $1/2$. Then some iteration $k$ of the main loop of Algorithm 1 has
--
--   $$P_k-\delta\ \le\ P^*\ \le\ P_k,$$
--
--   and $q^*$ is feasible for $\mathcal C_{P_k}$.
--
--   Differences from the source:
--   - generalization: q* an optimal division from Lemma 3.2 → every division q* with Σᵢ q*ᵢgᴰᵢ ≥ 0 and P* ≤ 1/2; reason: the optimal division of Lemma 3.2 has both properties
--   - encoding: Algorithm 1's inputs: divider values not all zero, standard deviations σᵢ > 0, an additive error bound γ → hypotheses gᴰ ≠ 0, σᵢ > 0, γ > 0; reason: the algorithm's own input conditions; γ ≤ 0 or gᴰ = 0 leaves δ ≤ 0 and the while loop does not terminate
-- source:
--   Tucker-Foltz & Zeckhauser, Playing Divide-and-Choose Given Uncertain Preferences, arXiv:2207.03076v2, Appendix C, p.32 ("on some iteration of Algorithm 1, P − δ ≤ P∗ ≤ P") and p.33 ("(q∗₁, …, q∗ₙ) is feasible for C_P")

import Mathlib
import Definitions.Def_DivideChooseBayes_IsDivision
import Definitions.Def_DivideChooseBayes_pileOneProb
import Definitions.Def_DivideChooseBayes_normalPrior
import Definitions.Def_DivideChooseBayes_cpFeasibleSet
import Definitions.Def_DivideChooseBayes_iterationCount

open MeasureTheory ProbabilityTheory

namespace DivideChooseBayes

/-- **Appendix C, pp.32–33: some iteration brackets `P*`, and `q*` is feasible there.**
Tucker-Foltz & Zeckhauser, *Playing Divide-and-Choose Given Uncertain Preferences*,
arXiv:2207.03076v2, Appendix C, p.32: "Therefore, on some iteration of Algorithm 1, P − δ ≤ P* ≤ P." and p.33:
"Observe that (q*₁, q*₂, …, q*ₙ) is feasible for C_P."

Under independent normal priors with `σᵢ > 0`, for `gᴰ` not all zero and `γ > 0`: if `q*` is a
division with `∑ᵢ q*ᵢgᴰᵢ ≥ 0` whose probability `P*` that the chooser picks pile 1 is at most `1/2`,
then some iteration `k` of the main loop has `P_k − δ ≤ P* ≤ P_k`, and `q*` is feasible for
`C_{P_k}`.

**Formalization Note.** The paper takes `q*` optimal (from Lemma 3.2); the statement holds for
every division with (3) and `P* ≤ 1/2`. The display on p.33 reads `Φ(P*) ≤ Φ(P)`, a typo for
`Φ⁻¹`; nothing of it is encoded. -/
theorem appendix_c_grid_feasible {ι : Type*} [Fintype ι] (gD m σ : ι → ℝ)
    (hgD : ∃ i, gD i ≠ 0) (hσ : ∀ i, 0 < σ i) (γ : ℝ) (hγ : 0 < γ) (qs : ι → ℝ)
    (hqs : IsDivision qs) (hw : 0 ≤ ∑ i, qs i * gD i)
    (hP : pileOneProb (normalPrior m σ) gD qs ≤ 1 / 2) :
    ∃ k < iterationCount gD γ,
      algP gD γ k - algDelta gD γ ≤ pileOneProb (normalPrior m σ) gD qs ∧
        pileOneProb (normalPrior m σ) gD qs ≤ algP gD γ k ∧
        qs ∈ cpFeasibleSet gD m σ (algP gD γ k) := by sorry

end DivideChooseBayes
