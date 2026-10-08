-- Prove2me | Theorems.Thm_DantzigSimplex_Technique_simplex_technique_terminates
-- name    : DantzigSimplex.Technique.simplex_technique_terminates
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:22:44.81298+00:00
-- url     : https://prove2.me/theorems/662b89cf-fb71-492c-b09d-2a6ffcc42b75
-- title:
--   The two-phase simplex technique terminates with a correct outcome
-- statement:
--   For the equality-form maximization problem (5)–(6), assume $1\le m\le n$, Dantzig's independence of every $m$ among $P_0,P_1,\ldots,P_n$, an initial strictly positive Phase I representation of a fixed reference point $G$, and general position of $G$. Run any sequence of the paper's admissible Phase I pivots, hand-off (39), and Phase II pivots. There is no infinite sequence of these transitions. Every state with no outgoing transition has one of the following outcomes:
--
--   1. It is in Phase I with $y_{0j}\le0$ for all $j$, and the original problem is infeasible.
--   2. It is in Phase II with an improving column $j$ such that $c_j>z_j$ and $x_{ij}\le0$ for all basic $i$; feasible objective values are unbounded above: for every $M\in\mathbb R$, some feasible $\lambda$ has $z(\lambda)>M$.
--   3. It is in Phase II with $c_j\le z_j$ for all $j$, and its current weights attain the maximum objective over all feasible weights.
--
--   This states the full two-phase outcome independent of the choice of an admissible entering column or minimizing leaving index. **Formalization Note** The general-position assumption is added because the printed Phase I argument requires strict positive basic weights after each pivot. Termination means absence of an infinite admissible run; infeasibility, unboundedness, and optimality concern the original linear program, not just a tableau.
-- source:
--   Dantzig, Maximization of a Linear Function of Variables Subject to Linear Inequalities, in Koopmans (ed.), Activity Analysis of Production and Allocation, Wiley 1951, Ch. XXI, pp. 340–347, Sections 1–2, conditions (17)–(18), (44)–(45)

import Mathlib
import Definitions.Def_DantzigSimplex_Technique_Process

namespace DantzigSimplex.Technique

/-- Sections 1--2: the complete Phase I/II procedure, (44)--(45) then (17)--(18). -/
theorem simplex_technique_terminates {m n : ℕ} (p : Problem m n)
    (hm : 1 ≤ m) (hmn : m ≤ n) (hnd : p.Nondegenerate)
    (G : Fin m → ℝ) (hgp : GeneralPosition p G)
    (initial : PhaseIState p G) :
    (¬ ∃ f : ℕ → SimplexState p G,
      ∀ k, SimplexStep (f k) (f (k + 1))) ∧
    (∀ s : SimplexState p G, Terminal s →
      (∃ u : PhaseIState p G, s = Sum.inl u ∧
        (∀ j, u.frame.y0 j ≤ 0) ∧ (∀ w, ¬ p.Feasible w)) ∨
      (∃ u : PhaseIIState p, s = Sum.inr u ∧
        ∃ j : Fin n, p.cost j > u.frame.z j ∧
          (∀ i ∈ u.frame.B, u.frame.x i j ≤ 0) ∧ p.Unbounded) ∨
      (∃ u : PhaseIIState p, s = Sum.inr u ∧
        (∀ j, p.cost j ≤ u.frame.z j) ∧ p.MaximumFeasible u.weight)) := by sorry

end DantzigSimplex.Technique
