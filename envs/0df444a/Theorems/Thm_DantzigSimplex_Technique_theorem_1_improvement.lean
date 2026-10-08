-- Prove2me | Theorems.Thm_DantzigSimplex_Technique_theorem_1_improvement
-- name    : DantzigSimplex.Technique.theorem_1_improvement
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:22:11.703999+00:00
-- url     : https://prove2.me/theorems/7bedf1c2-a861-4ded-b4db-8cf0a25e802f
-- title:
--   Theorem 1 — improving family, finite pivot or unbounded ray
-- statement:
--   Assume $1\le m\le n$ and Dantzig's nondegeneracy condition. Let $(B,\lambda)$ be a feasible Phase II state with exactly $m$ positive basic weights, and write $P_j=\sum_{i\in B}x_{ij}P_i$ and $z_j=\sum_{i\in B}x_{ij}c_i$. If $c_j>z_j$, the family (13) improves the objective at every positive feasible parameter:
--
--   $$
--   z(\lambda(\theta))=z(\lambda)+\theta(c_j-z_j)>z(\lambda),\qquad \theta>0.
--   $$
--
--   Moreover, exactly one of two cases holds. If some $x_{ij}>0$, then with $\theta_0=\min\{\lambda_i/x_{ij}: i\in B,\ x_{ij}>0\}$ attained at $i_0$ as in (16), the member $\lambda(\theta_0)$ of the family (13) for this same $j$ is a new feasible Phase II state on exactly the $m$ positive columns $(B\setminus\{i_0\})\cup\{j\}$, with a larger objective. If all $x_{ij}\le0$, feasible members of the family with exactly $m+1$ positive columns have objectives exceeding any prescribed real bound.
--
--   The two cases distinguish a finite pivot from an unbounded improving ray. **Formalization Note** The quantifier over positive $\theta$ in the first formula is restricted to feasible members of the named family; the unbounded case states arbitrary large objective on the original feasible set.
-- source:
--   Dantzig, Maximization of a Linear Function of Variables Subject to Linear Inequalities, in Koopmans (ed.), Activity Analysis of Production and Allocation, Wiley 1951, Ch. XXI, pp. 341–342, Theorem 1 and Eqs. (11)–(16)

import Mathlib
import Definitions.Def_DantzigSimplex_Technique_Process

namespace DantzigSimplex.Technique

/-- Theorem 1, pp. 341--342, with the two cases of (16) made explicit. -/
theorem theorem_1_improvement {m n : ℕ} (p : Problem m n)
    (hm : 1 ≤ m) (hmn : m ≤ n) (hnd : p.Nondegenerate)
    (s : PhaseIIState p) (j : Fin n) (hj : p.cost j > s.frame.z j) :
    (∀ θ : ℝ, 0 < θ → p.Feasible (phaseIIWeights s j θ) →
      p.objective s.weight < p.objective (phaseIIWeights s j θ)) ∧
    (((∃ i ∈ s.frame.B, 0 < s.frame.x i j) ∧
       ∃ (i₀ : Fin n) (θ : ℝ) (t : PhaseIIState p),
         i₀ ∈ s.frame.B ∧ 0 < s.frame.x i₀ j ∧
         θ = s.weight i₀ / s.frame.x i₀ j ∧
         (∀ i ∈ s.frame.B, 0 < s.frame.x i j →
           θ ≤ s.weight i / s.frame.x i j) ∧
         t.frame.B = insert j (s.frame.B.erase i₀) ∧
         t.weight = phaseIIWeights s j θ ∧
         p.objective s.weight < p.objective t.weight) ∨
    ((∀ i ∈ s.frame.B, s.frame.x i j ≤ 0) ∧
       ∀ M : ℝ, ∃ θ : ℝ, 0 < θ ∧
         p.Feasible (phaseIIWeights s j θ) ∧
         M < p.objective (phaseIIWeights s j θ) ∧
         (Finset.univ.filter (fun k => 0 < phaseIIWeights s j θ k)).card = m + 1)) := by sorry

end DantzigSimplex.Technique
