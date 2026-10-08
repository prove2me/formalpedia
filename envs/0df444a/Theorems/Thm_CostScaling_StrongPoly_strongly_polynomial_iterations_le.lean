-- Prove2me | Theorems.Thm_CostScaling_StrongPoly_strongly_polynomial_iterations_le
-- name    : CostScaling.StrongPoly.strongly_polynomial_iterations_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:14:43.336175+00:00
-- url     : https://prove2.me/theorems/b2927065-8732-4e14-a4d6-24a45d063c28
-- title:
--   Theorem 4.5 — at most m⌈log₂(2n)⌉ refinements reach minimum cost
-- statement:
--   Let $G=(V,E)$ be a finite symmetric circulation network with arbitrary real capacities and costs, $n=|V|\ge2$, and $m=|E|\ge n-1$. Start from a circulation $f_0$. At every step with $ε(f_k)>0$, suppose the next circulation $f_{k+1}$ is $ε(f_k)/2$-optimal. Then for some index $k$,
--
--   $$
--   k\le m\left\lceil\log_2(2n)\right\rceil,\qquad ε(f_k)=0,\qquad f_k\text{ is minimum-cost}.
--   $$
--
--   Thus the loop of Figure 3 makes at most $m\lceil\log_2(2n)\rceil$ calls to `refine` before it reaches a minimum-cost circulation. This is the explicit iteration form of the paper's $O(m\log n)$ result for real-valued data.
--
--   **Formalization Note** The factor two is the caption of Figure 3. The block length $\lceil\log_2(2n)\rceil$ is the first integer whose power of two reaches $2n$, and the proof of Theorem 4.5 allows at most $m$ such blocks, using Lemma 4.4. The function $ε(f)$ is the infimum of admissible errors; its attainment and the implication $ε(f)=0\Rightarrow f$ is minimum-cost are conclusions to establish, not added hypotheses. The reused 1989 reduced-cost sign is equivalent after $p\mapsto-p$.
-- source:
--   Goldberg & Tarjan, MIT/LCS/TM-333 (July 1987), Theorem 4.5 and proof, p. 17; Fig. 3, p. 15; standing assumption p. 5

import Mathlib
import Definitions.Def_CostScaling_StrongPoly_IsHalvingRun

namespace CostScaling.StrongPoly

open CycleCanceling.MinMean

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Theorem 4.5, p. 17, with the factor two of Figure 3 made explicit: within
`m * ⌈log₂(2n)⌉` refinements a halving run reaches zero tight error, and the
circulation at that point is minimum-cost. -/
theorem strongly_polynomial_iterations_le (N : CircNetwork V)
    (hvertices : 2 ≤ Fintype.card V)
    (harcs : Fintype.card V - 1 ≤ N.E.card)
    (f : ℕ → V → V → ℝ) (hrun : IsHalvingRun N f) :
    ∃ k : ℕ, k ≤ N.E.card * Nat.clog 2 (2 * Fintype.card V) ∧
      epsOpt N (f k) = 0 ∧ IsMinCost N (f k) := by sorry

end CostScaling.StrongPoly
