-- Prove2me | Theorems.Thm_DivideChooseBayes_appendix_c_iteration_value
-- name    : DivideChooseBayes.appendix_c_iteration_value
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:31:04.412217+00:00
-- url     : https://prove2.me/theorems/17dc5835-f1ec-4adf-9dad-1812fee132f6
-- title:
--   Appendix C, p.31 — each iteration's division achieves interim utility at least $u_P$
-- statement:
--   Let the chooser's values be independent with $g^C_i\sim\mathcal N(\mu_i,\sigma_i^2)$, $\sigma_i>0$, and let $g^D$ be the divider's values. For every $0<P\le 1/2$ and every point $q$ feasible for $\mathcal C_P$,
--
--   $$\mathbb E[u^D]\ \ge\ u_P(q)=\sum_{i=1}^n\frac{g^D_i}{2}\big(P(1-q_i)+(1-P)(1+q_i)\big),$$
--
--   where $\mathbb E[u^D]$ is the divider's interim expected utility of the division $q$.
--
--   Differences from the source:
--   - generalization: the optimal solution of C_P computed on an iteration, P = P_k → every feasible point q of C_P and every real 0 < P ≤ 1/2; reason: the iteration's solution is a feasible point and P_k ∈ (0, 1/2]
--   - encoding: E[uᴰ] of the division p computed by Algorithm 1 → the interim utility of the division in the variables q, p = (q + 1)/2; reason: the same division (Eqs. (1)–(2))
-- source:
--   Tucker-Foltz & Zeckhauser, Playing Divide-and-Choose Given Uncertain Preferences, arXiv:2207.03076v2, Appendix C, p.31 (claim) and pp.31–32 (proof)

import Mathlib
import Definitions.Def_DivideChooseBayes_normalPrior
import Definitions.Def_DivideChooseBayes_interimUtility
import Definitions.Def_DivideChooseBayes_cpObjective
import Definitions.Def_DivideChooseBayes_cpFeasibleSet

open MeasureTheory ProbabilityTheory

namespace DivideChooseBayes

/-- **Appendix C, p.31: each iteration's division achieves at least `u_P`.**
Tucker-Foltz & Zeckhauser, *Playing Divide-and-Choose Given Uncertain Preferences*,
arXiv:2207.03076v2, Appendix C, p.31: "We claim that, on each iteration of the main loop, the division
p₁, p₂, …, pₙ computed by Algorithm 1 achieves an interim expected utility of E[uᴰ] ≥ u_P."

Under independent normal priors with `σᵢ > 0`, for every `0 < P ≤ 1/2` and every feasible point
`q` of `C_P`, the divider's interim expected utility at `q` is at least the objective `u_P` at `q`.

**Formalization Note.** Stated for every feasible point and every real `0 < P ≤ 1/2`; the
iteration's optimal solution at `P = P_k` is a special case. Includes `q = 0`, where both sides
equal `∑ᵢ gᴰᵢ/2`. -/
theorem appendix_c_iteration_value {ι : Type*} [Fintype ι] (gD m σ : ι → ℝ)
    (hσ : ∀ i, 0 < σ i) (P : ℝ) (hP₀ : 0 < P) (hP : P ≤ 1 / 2) (q : ι → ℝ)
    (hq : q ∈ cpFeasibleSet gD m σ P) :
    cpObjective gD P q ≤ interimUtility (normalPrior m σ) gD q := by sorry

end DivideChooseBayes
