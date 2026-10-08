-- Prove2me | Theorems.Thm_DeterioratingJobs_Weighted_interchange_identity
-- name    : DeterioratingJobs.Weighted.interchange_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:39:52.887912+00:00
-- url     : https://prove2.me/theorems/6452a87f-47ab-4a3f-a879-ad265959e881
-- title:
--   Section 2, after Eq. (8) — adjacent-interchange cost identity
-- statement:
--   Consider a schedule $\pi$ with adjacent positions $j,j+1$ occupied by jobs $a,b$. Let $\pi_1$ interchange these positions, and let $S_{j-1}(\pi)$ be the completion time immediately before job $a$ starts. For every outcome,
--   $$
--   \begin{aligned}
--   C(\pi)-C(\pi_1)
--   ={}&S_{j-1}(\pi)[c_b\alpha_a(1+\alpha_b)-c_a\alpha_b(1+\alpha_a)]\\
--     &+[X_a c_b(1+\alpha_b)-X_b c_a(1+\alpha_a)]\\
--     &+\sum_{r=j+2}^{N}c_{\pi(r)}
--       \prod_{k=j+2}^{r}(1+\alpha_{\pi(k)})
--       [X_a\alpha_b-X_b\alpha_a].
--   \end{aligned}
--   $$
--   It gives the exact change in total weighted completion cost from interchanging two adjacent jobs.
--
--   **Formalization Note** The printed display is for the identity order and has a multiplication dot before its second bracket. The Lean statement applies to any permutation and replaces that dot with addition. For two jobs with $X=(1,2)$, $\alpha=(1,1)$ and $c=(2,1)$, the costs are $6$ and $12$, and both sides of the corrected identity equal $-6$.
-- source:
--   Browne, Yechiali, Scheduling Deteriorating Jobs on a Single Processor, Oper. Res. 38 (1990), p. 497, Section 2, unnumbered display between Eq. (8) and Proposition 2; https://doi.org/10.1287/opre.38.3.495

import Mathlib
import Definitions.Def_DeterioratingJobs_Weighted_Model

namespace DeterioratingJobs.Weighted

/-- The unnumbered interchange display between (8) and Proposition 2, p. 497.
The printed multiplication dot preceding the second bracket is corrected to addition. -/
theorem interchange_identity {Ω : Type*} {N : ℕ}
    (X : Fin N → Ω → ℝ) (α c : Fin N → ℝ)
    (π : Equiv.Perm (Fin N)) (p : Fin N) (hp : p.val + 1 < N) (ω : Ω) :
    let q : Fin N := ⟨p.val + 1, hp⟩
    let a := π p
    let b := π q
    let π₁ := π * Equiv.swap p q
    totalCost X α c π ω - totalCost X α c π₁ ω =
      DeterioratingJobs.Makespan.completionTime X α π p.val ω *
        (c b * α a * (1 + α b) - c a * α b * (1 + α a)) +
      (X a ω * c b * (1 + α b) - X b ω * c a * (1 + α a)) +
      ∑ r : Fin N with p.val + 2 ≤ r.val,
        c (π r) *
          (∏ k : Fin N with p.val + 2 ≤ k.val ∧ k ≤ r, (1 + α (π k))) *
          (X a ω * α b - X b ω * α a) := by sorry

end DeterioratingJobs.Weighted
