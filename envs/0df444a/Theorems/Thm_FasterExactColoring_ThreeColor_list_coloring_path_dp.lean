-- Prove2me | Theorems.Thm_FasterExactColoring_ThreeColor_list_coloring_path_dp
-- name    : FasterExactColoring.ThreeColor.list_coloring_path_dp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:12:11.589369+00:00
-- url     : https://prove2.me/theorems/dcf46c6d-f67e-4971-b369-2cbe9470806d
-- title:
--   Lemma 3.5 — randomized list-coloring path DP
-- statement:
--   Given any finite graph $G$, arbitrary lists in a palette of $k$ colors, and a valid supplied path decomposition of integer width $w$, one randomized program decides list colorability in time
--   $$O^*\!\left((\lfloor\Delta(G)/2\rfloor+1)^w\right).$$
--   Here $\Delta(G)$ is the maximum degree, set to zero for the empty graph. All description lengths, including the supplied decomposition and lists, are charged polynomially. Every coin tape halts within the claimed cost; no-instance acceptance has probability zero and yes-instance acceptance has probability at least $1/2$. The empty graph uses the constant-time width convention. This supplies the randomized clause of Lemma 4.8.
--
--   Differences from the source:
--   - encoding: finite simple graphs and colors labeled 1 through k → SimpleGraph (Fin n) with decidable adjacency and Fin k colors labeled from zero; reason: finite relabeling represents every source instance, including the empty graph
--   - encoding: uniform algorithm with O* runtime suppressing polynomial factors → one finite log-cost RAM program and uniform positive coefficient and natural polynomial exponent, with charged input, steps and output; reason: the source operations have polynomial bit cost; polynomial simulation overhead preserves the exponential bases
--   - encoding: (floor(Delta/2)+1)^pw → max(1,base)^max(0,width) for the time envelope; reason: the base is at least one, and a valid negative-width decomposition has an empty graph with base one; therefore the envelope equals the printed factor on every valid input, including zero palettes
--   - encoding: one-sided Monte Carlo success at least a fixed positive constant → success at least one half with worst-case halting on every finite fair coin tape; reason: independent constant repetition and charged amplification give the same O* bound
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Lemma 3.5, p. 4 (PDF p. 6)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_RuntimeBounds
import Definitions.Def_FasterExactColoring_ThreeColor_Decompositions

namespace FasterExactColoring.ThreeColor

theorem list_coloring_path_dp :
  ∃ (A : Program) (C : ℝ) (d : ℕ), 0 < C ∧
    ∀ (n k : ℕ) (G : GraphInput n) (L : Fin n → Finset (Fin k))
      (D : PathData n), D.valid G →
      let x := graphCode G ++ listCode L ++ D.code
      monteCarlo A x (polynomial C d x * widthFactor (maximumDegree G / 2 + 1) D.width)
        (listColorable G L) := by sorry

end FasterExactColoring.ThreeColor
