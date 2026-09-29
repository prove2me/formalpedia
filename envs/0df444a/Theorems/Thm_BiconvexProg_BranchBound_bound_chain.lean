-- Prove2me | Theorems.Thm_BiconvexProg_BranchBound_bound_chain
-- name    : BiconvexProg.BranchBound.bound_chain
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T17:57:03.945094+00:00
-- url     : https://prove2.me/theorems/b871c2ee-b4ba-46fc-bc71-e2fdc752a2d0
-- title:
--   The bound chain $v_b^1 \le v_b^2 \le \cdots \le v^* \le \cdots \le V_b^2 \le V_b^1$
-- statement:
--   Let $S, f, g, \Omega$ satisfy the standing hypotheses of Problem $\mathcal P$. Let $(x^*, y^*)$ be a global solution, with optimal value $v^* = \varphi(x^*, y^*)$. Along any run of the branch-and-bound algorithm, with best lower bounds $v_b^k$ and best upper bounds $V_b^k$,
--
--   $$v_b^1 \le v_b^2 \le \cdots \le v^* \le \cdots \le V_b^2 \le V_b^1 .$$
--
--   That is, $(v_b^k)$ is nondecreasing, $(V_b^k)$ is nonincreasing, and $v_b^k \le v^* \le V_b^k$ at every stage $k$.
--
--   The chain brackets the unknown optimal value between two monotone sequences computed by the algorithm. The convergence theorem shows that both converge to $v^*$.
--
--   **Formalization Note** Stages are numbered from $0$. $V_b^k = \min_{l \le k} \varphi(x^l, y^l)$.
-- source:
--   Al-Khayyal, Falk, Jointly Constrained Biconvex Programming, Math. Oper. Res. 8(2), 1983, p. 279, display after the Best Bound Rule

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_run

namespace BiconvexProg.BranchBound

/-- The bound chain (p. 279): along a run, the best lower bounds `v_bᵏ` are nondecreasing, the
best upper bounds `V_bᵏ` are nonincreasing, and `v_bᵏ ≤ v* ≤ V_bᵏ` for every stage, where
`v* = φ(z*)` is the optimal value of Problem 𝒫. -/
theorem bound_chain {n : ℕ} {S : Set ((Fin n → ℝ) × (Fin n → ℝ))} {f g : (Fin n → ℝ) → ℝ}
    {Ω : Box n} (hP : IsProblemP S f g Ω)
    {nodes : ℕ → Multiset (Box n)} {sel : ℕ → Box n} {idx : ℕ → Fin n}
    {pt : ℕ → (Fin n → ℝ) × (Fin n → ℝ)} (hrun : IsRun S f g Ω nodes sel idx pt)
    (zstar : (Fin n → ℝ) × (Fin n → ℝ)) (hzs : zstar ∈ S ∩ Ω.toSet)
    (hmin : IsMinOn (objective f g) (S ∩ Ω.toSet) zstar) :
    Monotone (bestLower f g sel pt) ∧ Antitone (bestUpper f g pt) ∧
      ∀ k, bestLower f g sel pt k ≤ objective f g zstar ∧
        objective f g zstar ≤ bestUpper f g pt k := by sorry

end BiconvexProg.BranchBound
