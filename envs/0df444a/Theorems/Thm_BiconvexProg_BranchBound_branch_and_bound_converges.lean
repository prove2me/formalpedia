-- Prove2me | Theorems.Thm_BiconvexProg_BranchBound_branch_and_bound_converges
-- name    : BiconvexProg.BranchBound.branch_and_bound_converges
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T18:00:51.005984+00:00
-- url     : https://prove2.me/theorems/3308dcae-b226-42b1-8b47-e7fc659dd4b1
-- title:
--   Convergence theorem — the convex-envelope branch-and-bound algorithm converges to a global solution of Problem $\mathcal P$
-- statement:
--   Let $S \subseteq \mathbb{R}^n \times \mathbb{R}^n$ be closed and convex, let $\Omega = \{(x,y) : l \le x \le L,\ m \le y \le M\}$ with $l \le L$ and $m \le M$, and let $f$ and $g$ be convex and continuous on $\{x : l \le x \le L\}$ and $\{y : m \le y \le M\}$. Assume $S \cap \Omega \ne \emptyset$ and $n > 0$. Consider Problem $\mathcal P$,
--
--   $$\min\ \varphi(x,y) = f(x) + x^\top y + g(y) \quad \text{subject to } (x,y) \in S \cap \Omega .$$
--
--   Run the branch-and-bound algorithm of Al-Khayyal and Falk. It starts from $\Omega$, lower-bounds each node $B$ by $\psi^B = f + \mathrm{Vex}_B\, x^\top y + g$, selects an open node by the Best Bound Rule, and splits it at its subproblem solution along the coordinate with the largest gap $x_i y_i - \mathrm{Vex}_{B_i}\, x_i y_i$. Let $(x^k, y^k)$ be the stage points, $v_b^k$ the best lower bounds and $V_b^k$ the best upper bounds. Then:
--
--   1. every accumulation point $(\bar x, \bar y)$ of $\big((x^k, y^k)\big)_k$ lies in $S \cap \Omega$ and is a global solution of Problem $\mathcal P$;
--   2. the optimal value $v^* = \min_{S \cap \Omega} \varphi$ is attained, and
--   $$\lim_{k\to\infty} v_b^k = v^* = \lim_{k \to \infty} V_b^k .$$
--
--   The paper never states this as one sentence. It announces on p. 279 that "the best lower bounds increase towards $v^*$, while the best upper bounds decrease towards $v^*$. It remains to show that the procedure converges to a global solution", and its convergence proof ends with $\bar\psi(\bar x,\bar y) = \varphi(\bar x,\bar y)$ at a limit point of any convergent subsequence of stage points. Part 1 is what convergence to a global solution means for an infinite branch-and-bound procedure. Part 2 makes precise the two monotone limits of p. 279.
--
--   **Formalization Note** Runs are infinite and ignore the stopping test; a run the paper stops is a prefix of such a run. Stages are numbered from $0$. Continuity of $f$ and $g$ is an added hypothesis that the paper takes for granted. The optional pruning of p. 278 is omitted. The paper's proof relies on two intermediate claims that are false as printed, the well-definedness of the stage function on shared faces (p. 277) and the equicontinuity of the stage functions (p. 282). Only the theorem, not that proof, is formalized.
-- source:
--   Al-Khayyal, Falk, Jointly Constrained Biconvex Programming, Math. Oper. Res. 8(2), 1983, pp. 279–282, Convergence proof (announced p. 279; concluding identity p. 280)

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_run

namespace BiconvexProg.BranchBound

open Filter Topology

/-- Convergence theorem ("Convergence proof", pp. 279–282): along every run of the convex-envelope
branch-and-bound algorithm on Problem 𝒫,
1. every accumulation point of the stage points `(xᵏ, yᵏ)` is feasible and globally minimises
   `φ` over `S ∩ Ω`;
2. the best lower bounds `v_bᵏ` and 3. the best upper bounds `V_bᵏ` converge to the optimal value
   `v*`. -/
theorem branch_and_bound_converges {n : ℕ} {S : Set ((Fin n → ℝ) × (Fin n → ℝ))}
    {f g : (Fin n → ℝ) → ℝ} {Ω : Box n} (hP : IsProblemP S f g Ω)
    {nodes : ℕ → Multiset (Box n)} {sel : ℕ → Box n} {idx : ℕ → Fin n}
    {pt : ℕ → (Fin n → ℝ) × (Fin n → ℝ)} (hrun : IsRun S f g Ω nodes sel idx pt) :
    (∀ zbar, MapClusterPt zbar atTop pt →
      zbar ∈ S ∩ Ω.toSet ∧ IsMinOn (objective f g) (S ∩ Ω.toSet) zbar) ∧
    ∃ vstar : ℝ, (∃ z ∈ S ∩ Ω.toSet, objective f g z = vstar) ∧
      (∀ z ∈ S ∩ Ω.toSet, vstar ≤ objective f g z) ∧
      Tendsto (bestLower f g sel pt) atTop (𝓝 vstar) ∧
      Tendsto (bestUpper f g pt) atTop (𝓝 vstar) := by sorry

end BiconvexProg.BranchBound
