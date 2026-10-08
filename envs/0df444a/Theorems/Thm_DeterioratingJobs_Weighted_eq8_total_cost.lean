-- Prove2me | Theorems.Thm_DeterioratingJobs_Weighted_eq8_total_cost
-- name    : DeterioratingJobs.Weighted.eq8_total_cost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:39:33.911399+00:00
-- url     : https://prove2.me/theorems/45e13679-2f9e-4215-b2d3-e7b412b8cb98
-- title:
--   Equation (8) — weighted completion cost under linear deterioration
-- statement:
--   In the linear deterioration model, let $c_i$ be job $i$'s waiting cost rate and $C(\pi)$ the sum of each job's rate times its completion time. For any schedule $\pi$ and every outcome,
--   $$
--   C(\pi)=\sum_{k=1}^{N}c_{\pi(k)}
--     \sum_{i=1}^{k}X_{\pi(i)}
--     \prod_{r=i+1}^{k}(1+\alpha_{\pi(r)}).
--   $$
--   This is the objective whose expectation Proposition 2 minimizes.
--
--   **Formalization Note** Equation (8) is printed for the identity schedule $\pi_0$; the statement relabels it along any permutation. The weight is attached to the job $\pi(k)$, not the position $k$. It is a pathwise identity and requires no integrability hypothesis.
-- source:
--   Browne, Yechiali, Scheduling Deteriorating Jobs on a Single Processor, Oper. Res. 38 (1990), p. 497, Section 2, Eq. (8); https://doi.org/10.1287/opre.38.3.495

import Mathlib
import Definitions.Def_DeterioratingJobs_Weighted_Model

namespace DeterioratingJobs.Weighted

/-- Equation (8), p. 497, relabelled along an arbitrary schedule. -/
theorem eq8_total_cost {Ω : Type*} {N : ℕ}
    (X : Fin N → Ω → ℝ) (α c : Fin N → ℝ)
    (π : Equiv.Perm (Fin N)) (ω : Ω) :
    totalCost X α c π ω =
      ∑ k : Fin N, c (π k) *
        ∑ i : Fin N with i ≤ k,
          X (π i) ω * ∏ r : Fin N with i < r ∧ r ≤ k, (1 + α (π r)) := by sorry

end DeterioratingJobs.Weighted
