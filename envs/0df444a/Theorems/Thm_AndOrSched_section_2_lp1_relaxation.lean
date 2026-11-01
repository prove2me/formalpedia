-- Prove2me | Theorems.Thm_AndOrSched_section_2_lp1_relaxation
-- name    : AndOrSched.section_2_lp1_relaxation
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:32:11.217439+00:00
-- url     : https://prove2.me/theorems/794454a9-557d-4650-843c-f1bc093f60bb
-- title:
--   §2, p.7 — LP (1) is a relaxation
-- statement:
--   Let $I$ be a normalized instance with acyclic AND-precedences and $p_j\le1$ for all $j$. Then LP (1) has an optimal solution $\bar x$, and for every optimal $\bar x$ and every feasible schedule $C$,
--   $$\sum_{b\in B}w_b\bar C_b\;\le\;\sum_{j\in N}w_jC_j .$$
--   So the LP value is a lower bound on the optimal value of the scheduling problem.
--
--   Differences from the source:
--   - encoding: a precedence digraph E∧ → hypothesis `Acyclic I`; reason: a precedence graph is acyclic; the paper's transitive-closure and redundancy assumptions presuppose it
--   - reading: the page presupposes an optimal fractional solution x̄ → existence of an optimal solution is a clause of the statement; reason: the algorithm needs it, and the bound alone would be vacuous without it
--   - encoding: lower bound on the optimal objective value → bound against the cost of every feasible schedule (idle time and non-integer completion times allowed); reason: equivalent, and avoids an infimum
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §2, p.7, "Note that Σj wjC̄j is a lower bound on the objective value of an optimal integer solution, which corresponds to an optimal schedule."

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_Acyclic
import Definitions.Def_AndOrSched_IsFeasible
import Definitions.Def_AndOrSched_cost
import Definitions.Def_AndOrSched_IsNormalized
import Definitions.Def_AndOrSched_LP1Obj
import Definitions.Def_AndOrSched_LP1Optimal
open scoped Classical NNReal

namespace AndOrSched

/-- §2, p.7 (Happach, Schulz, arXiv:2001.07011v1): "Note that Σj wjC̄j is a lower bound on the objective value of an optimal integer
solution, which corresponds to an optimal schedule."

For a normalized instance with acyclic AND-precedences and processing times at most `1`, LP (1) has
an optimal solution, and the objective value `Σ_b w_b C̄_b` of every optimal solution is at most the
cost of every feasible schedule.

**Formalization Note** The cost of a normalized instance counts `B`-jobs only, since `w_a = 0` on
`A`. Feasible schedules may have idle time and non-integer completion times. -/
theorem section_2_lp1_relaxation (I : Instance) (hI : Acyclic I) (hN : IsNormalized I)
    (hp : ∀ j, I.p j ≤ 1) :
    (∃ x, LP1Optimal I x) ∧
    ∀ x, LP1Optimal I x → ∀ C : I.N → ℝ, IsFeasible I C → LP1Obj I x ≤ cost I C := by sorry

end AndOrSched
