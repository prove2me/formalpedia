-- Prove2me | Theorems.Thm_DeterioratingJobs_Weighted_proposition2
-- name    : DeterioratingJobs.Weighted.proposition2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:39:32.870827+00:00
-- url     : https://prove2.me/theorems/a30d0fb8-d587-4dd5-919a-d27506bfa320
-- title:
--   Proposition 2 — two increasing indices make the identity order optimal for weighted expected completion cost
-- statement:
--   Let $N$ jobs have nonnegative random initial processing requirements $X_i$ with finite expectations, positive linear deterioration rates $\alpha_i$, and positive waiting cost rates $c_i$. Suppose both job-indexed chains are strict:
--   $$
--   \frac{E(X_1)}{\alpha_1}<\cdots<\frac{E(X_N)}{\alpha_N},
--   \qquad
--   \frac{\alpha_1}{c_1(1+\alpha_1)}
--     <\cdots<
--   \frac{\alpha_N}{c_N(1+\alpha_N)}.
--   $$
--   Then the identity order $\pi_0=(1,\ldots,N)$ minimizes the weighted expected completion cost over every permutation $\sigma$:
--   $$
--   E[C(\pi_0)]\le E[C(\sigma)].
--   $$
--   This is the paper's sufficient rule for a weighted completion objective under linear deterioration.
--
--   **Formalization Note** Expected cost is the Bochner integral of the recursively defined pathwise cost on a probability space. Each $X_i$ is integrable; nonnegativity is stated pointwise, matching the paper's standing positive processing-requirement convention. Positive $\alpha_i$ and $c_i$ make both indices meaningful and are needed for the rule. The two strict chains are over job labels, and the conclusion compares $\pi_0$ with every permutation, including nonadjacent reorderings. No independence assumption is imposed.
-- source:
--   Browne, Yechiali, Scheduling Deteriorating Jobs on a Single Processor, Oper. Res. 38 (1990), p. 497, Proposition 2, with the standing model on pp. 495–496; https://doi.org/10.1287/opre.38.3.495

import Mathlib
import Definitions.Def_DeterioratingJobs_Weighted_Model

namespace DeterioratingJobs.Weighted

open MeasureTheory

/-- Proposition 2, p. 497: identity order minimizes expected weighted completion cost. -/
theorem proposition2 {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin N → Ω → ℝ) (α c : Fin N → ℝ)
    (hX : ∀ i, Integrable (X i) P)
    (hX0 : ∀ i ω, 0 ≤ X i ω)
    (hα : ∀ i, 0 < α i) (hc : ∀ i, 0 < c i)
    (hindex : StrictMono (fun i : Fin N => (∫ ω, X i ω ∂P) / α i))
    (hcost : StrictMono (fun i : Fin N => α i / (c i * (1 + α i)))) :
    ∀ σ : Equiv.Perm (Fin N),
      (∫ ω, totalCost X α c 1 ω ∂P) ≤
        ∫ ω, totalCost X α c σ ω ∂P := by sorry

end DeterioratingJobs.Weighted
