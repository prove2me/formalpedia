-- Prove2me | Theorems.Thm_FasterExactColoring_ThreeColor_degree_three_cycle_reduction
-- name    : FasterExactColoring.ThreeColor.degree_three_cycle_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:11:46.172894+00:00
-- url     : https://prove2.me/theorems/502c4f95-d6f0-43db-9054-4bdcf90c9c7e
-- title:
--   Lemma 4.1 — degree-three cycle branching
-- statement:
--   Let $G$ be any finite simple graph containing a cycle all of whose vertices have ambient degree three. There is one deterministic polynomial-time program which outputs finitely many strictly smaller graph instances $G_i$, preserving the decision problem in both directions:
--   $$G\text{ is 3-colorable}\iff\exists i,\ G_i\text{ is 3-colorable},\qquad
--   \sum_i\lambda_{\rm cycle}^{|V(G_i)|-|V(G)|}\le1.$$
--   Here $\lambda_{\rm cycle}=\lambda(5,6,7,8)$ satisfies $1<\lambda_{\rm cycle}\le1.2434$. All branch construction and output costs are charged. This supplies the degree-three-cycle preprocessing reduction.
--
--   Differences from the source:
--   - encoding: finite simple graphs and colors labeled 1 through k → SimpleGraph (Fin n) with decidable adjacency and Fin k colors labeled from zero; reason: finite relabeling represents every source instance, including the empty graph
--   - encoding: uniform algorithm with O* runtime suppressing polynomial factors → one finite log-cost RAM program and uniform positive coefficient and natural polynomial exponent, with charged input, steps and output; reason: the source operations have polynomial bit cost; polynomial simulation overhead preserves the exponential bases
--   - encoding: work factor at most lambda(5,6,7,8) → sum of lambda_cycle^(child order minus parent order) at most one, with strictly smaller children and equisatisfiability; reason: the source definition of work factor uses vertex count as its measure
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Lemma 4.1, p. 5 (PDF p. 7)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_RuntimeBounds

namespace FasterExactColoring.ThreeColor

theorem degree_three_cycle_reduction :
  1 < cycleBase ∧ cycleBase ≤ (6217/5000 : ℝ) ∧
  ∃ (A : Program) (C : ℝ) (d : ℕ), 0 < C ∧ deterministic A ∧
    ∀ (n : ℕ) (G : GraphInput n), degreeThreeCycle G →
      runWithin A (graphCode G) (polynomial C d (graphCode G))
        (fun y => ∃ branches : List (Σ k : ℕ, GraphInput k),
          y = branches.length :: branches.flatMap (fun H => graphCode H.2) ∧
          (∀ H ∈ branches, H.1 < n) ∧
          (colorable G 3 ↔ ∃ H ∈ branches, colorable H.2 3) ∧
          (branches.map (fun H => cycleBase^((H.1:ℝ)-n))).sum ≤ 1) := by sorry

end FasterExactColoring.ThreeColor
