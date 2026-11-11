-- Prove2me | Theorems.Thm_FasterExactColoring_ThreeColor_degree_sequence_decomposition
-- name    : FasterExactColoring.ThreeColor.degree_sequence_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:11:54.211299+00:00
-- url     : https://prove2.me/theorems/1c891fae-7a57-436d-a5e7-d5cf5f8e05e6
-- title:
--   Lemma 3.6 — constructive degree-sequence path decomposition
-- statement:
--   For every fixed $\varepsilon>0$, one deterministic polynomial-time program constructs a path decomposition of every finite simple graph $G$ on $n$ vertices with width
--   $$w\le\frac{n_3}{6}+\frac{n_4}{3}+\frac{13n_5}{30}+\frac{23n_6}{45}+n_{\ge7}+\varepsilon n+K_\varepsilon.$$
--   Here $n_i$ counts vertices of degree $i$ and $n_{\ge7}$ counts vertices of degree at least seven. The additive constant $K_\varepsilon\ge0$, polynomial constants and program depend on $\varepsilon$ only. Output is an actual valid bag sequence, whose complete output cost is charged. The empty graph is included. This is the constructive width tool used for residual components.
--
--   Differences from the source:
--   - encoding: finite simple graphs and colors labeled 1 through k → SimpleGraph (Fin n) with decidable adjacency and Fin k colors labeled from zero; reason: finite relabeling represents every source instance, including the empty graph
--   - encoding: uniform algorithm with O* runtime suppressing polynomial factors → one finite log-cost RAM program and uniform positive coefficient and natural polynomial exponent, with charged input, steps and output; reason: the source operations have polynomial bit cost; polynomial simulation overhead preserves the exponential bases
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Lemma 3.6, p. 4 (PDF p. 6)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_RuntimeBounds
import Definitions.Def_FasterExactColoring_ThreeColor_Decompositions

namespace FasterExactColoring.ThreeColor

theorem degree_sequence_decomposition (ε : ℝ) (hε : 0 < ε) :
  ∃ (A : Program) (C K : ℝ) (d : ℕ), 0 < C ∧ 0 ≤ K ∧ deterministic A ∧
    ∀ (n : ℕ) (G : GraphInput n),
      runWithin A (graphCode G) (polynomial C d (graphCode G))
        (fun y => ∃ D : PathData n, y = D.code ∧ D.valid G ∧
          (D.width : ℝ) ≤ degreeSequenceBound G + ε*n + K) := by sorry

end FasterExactColoring.ThreeColor
