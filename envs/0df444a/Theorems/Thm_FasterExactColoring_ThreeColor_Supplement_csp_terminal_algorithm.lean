-- Prove2me | Theorems.Thm_FasterExactColoring_ThreeColor_Supplement_csp_terminal_algorithm
-- name    : FasterExactColoring.ThreeColor.Supplement.csp_terminal_algorithm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:53:44.197955+00:00
-- url     : https://prove2.me/theorems/ea8c49ed-3135-460a-8e20-e90dd2aedcab
-- title:
--   Lemma 5.4 (used in the proof of Theorem 1.3) — CSP terminal algorithm
-- statement:
--   There are one deterministic program and constants $C>0,d\in\mathbb N$ deciding every valid terminal restricted four-coloring instance with its valid maximal star packings in a polynomial in the encoded input size times
--   $$3^{s_{\star1}/4}\Bigl(\prod_{i=0}^3g_{3,i}^{a_i}\Bigr)
--    \Bigl(\prod_{i=0}^4g_{4,i}^{b_i}\Bigr)\Lambda^{s'}e^{h(a_0)}.$$
--   Here $a_i,b_i$ are the computed clique counts, $s'=|S'|$, and $\Lambda$ is the published exact CSP root. All cases are retained:
--   $$g_{m,0}=3m/2,\quad g_{m,1}=\Lambda^{m-1}(3+\Lambda^3),\quad
--    g_{m,i}=\frac6{(4-i)!}(4-i+i\Lambda^3)\ (2\le i\le m),\quad m\in\{3,4\}.$$
--   The explicit $h$ from Lemma 5.3 acts on the $a_0$ covered triangles and is uniformly sublinear in the original order, since $a_0\le n/3$. The factor $e^{o(n)}$ is retained. This is the CSP member of the terminal algorithm portfolio.
--
--   Differences from the source:
--   - encoding: terminal instances after the two maximal-star preprocessing steps → valid restricted instances with supplied valid inclusion-maximal star packings, all structural counts computed from them; reason: the explicit finite input includes the graph, restrictions and packings; its size is polynomial in the original vertex count
--   - encoding: an exp(o(n)) overhead from the triangle-cover construction → exp(h(a_0)) with h the explicit block envelope of Lemma 5.3; reason: exactly a_0 triangles require that cover, and a_0 at most n/3 makes this uniformly subexponential in original order
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Lemma 5.4, p. 12 (PDF p. 14)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_Supplement_TerminalBounds

set_option autoImplicit false

namespace FasterExactColoring.ThreeColor.Supplement

theorem csp_terminal_algorithm :
  ∃ (A : Program) (C : ℝ) (d : ℕ), 0 < C ∧
    terminalSolver .det A C d (fun P K => cspTerminalFactor P K) := by sorry

end FasterExactColoring.ThreeColor.Supplement
