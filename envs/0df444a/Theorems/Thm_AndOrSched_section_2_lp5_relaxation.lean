-- Prove2me | Theorems.Thm_AndOrSched_section_2_lp5_relaxation
-- name    : AndOrSched.section_2_lp5_relaxation
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:33:05.238555+00:00
-- url     : https://prove2.me/theorems/770bd701-f3bd-4cab-9722-7514a89a32ba
-- title:
--   §2, p.9 — LP (5) is a relaxation (corrected: (5f) with $\tau_l\ge p_j$)
-- statement:
--   Let $I$ be a normalized instance with acyclic AND-precedences and let $\varepsilon'>0$. Then LP (5) (with the corrected (5f)) has an optimal solution, and for every optimal $\bar x$ and every feasible schedule $C$,
--   $$\sum_{b\in B}w_b\bar C_b\;\le\;\sum_{j\in N}w_jC_j .$$
--
--   Differences from the source:
--   - correction: (5f): x_jl ≥ 0 for l ∈ [L] with τ_{l−1} ≥ p_j (other variables absent) → x_jl ≥ 0 for all l ∈ [L], and x_jl = 0 when τ_l < p_j; reason: as printed LP (5) is infeasible for A = {a}, B = {b}, p_a = 2, p_b = 0, P(b) = {a}, E∧ = ∅, ε′ = 1/2 (τ = (1, 1, 1.5, 2.25), L = 3, no l has τ_{l−1} ≥ 2), although the instance has a feasible schedule; a job completing in (τ_{l−1}, τ_l] has p_j ≤ τ_l
--   - encoding: a precedence digraph E∧ → hypothesis `Acyclic I`; reason: a precedence graph is acyclic; the paper's transitive-closure and redundancy assumptions presuppose it
--   - reading: the page presupposes an optimal fractional solution x̄ → existence of an optimal solution is a clause of the statement; reason: the algorithm needs it
--   - encoding: lower bound on the optimal value of a feasible schedule → bound against the cost of every feasible schedule; reason: equivalent, and avoids an infimum
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §2, p.9, "Note that Σj wj C̄j is a lower bound on the optimal objective value of an integer solution, which is a lower bound on the optimal value of a feasible schedule."

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_Acyclic
import Definitions.Def_AndOrSched_IsFeasible
import Definitions.Def_AndOrSched_cost
import Definitions.Def_AndOrSched_IsNormalized
import Definitions.Def_AndOrSched_LP5Obj
import Definitions.Def_AndOrSched_LP5Optimal
open scoped Classical NNReal

namespace AndOrSched

/-- §2, p.9 (Happach, Schulz, arXiv:2001.07011v1): "Note that Σj wj C̄j is a lower bound on the optimal objective value of an integer
solution, which is a lower bound on the optimal value of a feasible schedule."

For a normalized instance with acyclic AND-precedences and every `ε' > 0`, LP (5) (with corrected
(5f)) has an optimal solution, and the objective value `Σ_b w_b C̄_b` of every optimal solution is at
most the cost of every feasible schedule.

**Formalization Note** (5f) is corrected from `τ_{l−1} ≥ pⱼ` to `τ_l ≥ pⱼ`; as printed, LP (5) is
infeasible on some instances (see `LP5Feasible`). -/
theorem section_2_lp5_relaxation (I : Instance) (hI : Acyclic I) (hN : IsNormalized I)
    (ε' : ℝ) (hε' : 0 < ε') :
    (∃ x, LP5Optimal I ε' x) ∧
    ∀ x, LP5Optimal I ε' x → ∀ C : I.N → ℝ, IsFeasible I C → LP5Obj I ε' x ≤ cost I C := by sorry

end AndOrSched
