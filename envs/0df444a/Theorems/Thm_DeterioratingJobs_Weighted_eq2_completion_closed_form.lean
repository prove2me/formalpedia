-- Prove2me | Theorems.Thm_DeterioratingJobs_Weighted_eq2_completion_closed_form
-- name    : DeterioratingJobs.Weighted.eq2_completion_closed_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:39:12.765132+00:00
-- url     : https://prove2.me/theorems/9b098e42-6ed9-4d9d-931f-77dfb68c3775
-- title:
--   Equation (2) — completion time as a sum of deteriorated initial requirements
-- statement:
--   Let $\pi$ be any ordering of $N$ jobs, with initial processing requirements $X_i$ and linear deterioration rates $\alpha_i$. The time $S_k(\pi)$ after its first $k$ jobs satisfies, for $0\le k\le N$ and every outcome,
--   $$
--   S_k(\pi)=\sum_{i=1}^{k}X_{\pi(i)}\prod_{r=i+1}^{k}(1+\alpha_{\pi(r)}).
--   $$
--   An empty product equals one. This identifies how each initial requirement contributes to later completion times.
--
--   **Formalization Note** The paper writes the formula for the identity order $\pi_0=(1,\ldots,N)$; the statement relabels the same recursion along any permutation. It is pathwise, so it requires no probability or positivity hypothesis. The $k=0$ case is the empty sum.
-- source:
--   Browne, Yechiali, Scheduling Deteriorating Jobs on a Single Processor, Oper. Res. 38 (1990), p. 496, Section 1, Eq. (2); https://doi.org/10.1287/opre.38.3.495

import Mathlib
import Definitions.Def_DeterioratingJobs_Weighted_Model

namespace DeterioratingJobs.Weighted

/-- Equation (2), p. 496, relabelled along an arbitrary schedule. -/
theorem eq2_completion_closed_form {Ω : Type*} {N : ℕ}
    (X : Fin N → Ω → ℝ) (α : Fin N → ℝ) (π : Equiv.Perm (Fin N))
    (k : ℕ) (hk : k ≤ N) (ω : Ω) :
    DeterioratingJobs.Makespan.completionTime X α π k ω =
      ∑ i : Fin N with i.val < k,
        X (π i) ω * ∏ r : Fin N with i < r ∧ r.val < k, (1 + α (π r)) := by sorry

end DeterioratingJobs.Weighted
