-- Prove2me | Theorems.Thm_FasterExactColoring_ThreeColor_csp_running_time
-- name    : FasterExactColoring.ThreeColor.csp_running_time
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:11:49.893134+00:00
-- url     : https://prove2.me/theorems/b26b0f8c-1521-4963-a73b-1c07569443b9
-- title:
--   Lemma 4.7 — CSP running time
-- statement:
--   There is one deterministic program deciding 3-colorability of every graph after forest preprocessing. Choose one internal root per tree and compute $p,q,s,t,d,c$ as in the source; $c$ is the largest number of degree-three vertices in a residual component. With $B_I=3^p2^q$, its running time is
--   $$O^*\!\left(B_I\Lambda^{s+t}(3\Lambda^{-4})^{(d+t)/10+19c/660}\right).$$
--   The program, positive polynomial coefficient and polynomial degree are fixed before the graph, forest and roots. Its answer is yes if and only if the graph is 3-colorable. The root $\Lambda$ and coefficient $19/660$ are exact. This gives the CSP alternative in the final running-time comparison.
--
--   Differences from the source:
--   - encoding: finite simple graphs and colors labeled 1 through k → SimpleGraph (Fin n) with decidable adjacency and Fin k colors labeled from zero; reason: finite relabeling represents every source instance, including the empty graph
--   - encoding: uniform algorithm with O* runtime suppressing polynomial factors → one finite log-cost RAM program and uniform positive coefficient and natural polynomial exponent, with charged input, steps and output; reason: the source operations have polynomial bit cost; polynomial simulation overhead preserves the exponential bases
--   - encoding: graph after the preprocessing of Section 4.2 → minimum degree three, acyclicity of ambient degree-three vertices, and a modified maximal bushy forest; valid internal roots and a maximal leaf matching where used; reason: these are exactly the source standing conditions, and counts are computed rather than assumed independent
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Lemma 4.7, p. 8 (PDF p. 10)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_RuntimeBounds

namespace FasterExactColoring.ThreeColor

theorem csp_running_time :
  ∃ (A : Program) (C : ℝ) (d : ℕ), 0 < C ∧
    deterministic A ∧ ∀ (n : ℕ) (G : GraphInput n) (F : ForestData n)
      (roots : Finset (Fin n)), forestPreprocessed G F → F.rooted roots →
      let x := graphCode G ++ F.code ++ vertexSetCode roots
      runWithin A x (polynomial C d x * cspFactor (counts G F roots ∅))
        (answers (colorable G 3)) := by sorry

end FasterExactColoring.ThreeColor
