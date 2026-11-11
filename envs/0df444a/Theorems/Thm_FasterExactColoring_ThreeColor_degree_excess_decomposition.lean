-- Prove2me | Theorems.Thm_FasterExactColoring_ThreeColor_degree_excess_decomposition
-- name    : FasterExactColoring.ThreeColor.degree_excess_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:12:28.719753+00:00
-- url     : https://prove2.me/theorems/08eab772-66db-408d-a36e-8952b52437c5
-- title:
--   Lemma 3.7 — constructive degree-excess decomposition
-- statement:
--   For every fixed $\varepsilon>0$, one deterministic polynomial-time program constructs a path decomposition of every finite simple graph $G$ on $n$ vertices with integer width
--   $$w\le\frac16\sum_{v\in V(G)}\max\{\deg_G(v)-2,0\}+\varepsilon n+K_\varepsilon.$$
--   There is no maximum-degree restriction. The additive loss, program and polynomial constants may depend on $\varepsilon$ only. The output is the complete valid decomposition; its output cost is part of the polynomial time bound. This applies to the graph formed by unmatched leaves together with the residual vertices.
--
--   Differences from the source:
--   - encoding: finite simple graphs and colors labeled 1 through k → SimpleGraph (Fin n) with decidable adjacency and Fin k colors labeled from zero; reason: finite relabeling represents every source instance, including the empty graph
--   - encoding: uniform algorithm with O* runtime suppressing polynomial factors → one finite log-cost RAM program and uniform positive coefficient and natural polynomial exponent, with charged input, steps and output; reason: the source operations have polynomial bit cost; polynomial simulation overhead preserves the exponential bases
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Lemma 3.7, p. 4 (PDF p. 6)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_RuntimeBounds
import Definitions.Def_FasterExactColoring_ThreeColor_Decompositions

namespace FasterExactColoring.ThreeColor

theorem degree_excess_decomposition (ε : ℝ) (hε : 0 < ε) :
  ∃ (A : Program) (C K : ℝ) (d : ℕ), 0 < C ∧ 0 ≤ K ∧ deterministic A ∧
    ∀ (n : ℕ) (G : GraphInput n),
      runWithin A (graphCode G) (polynomial C d (graphCode G))
        (fun y => ∃ D : PathData n, y = D.code ∧ D.valid G ∧
          (D.width : ℝ) ≤ degreeExcessBound G + ε*n + K) := by sorry

end FasterExactColoring.ThreeColor
