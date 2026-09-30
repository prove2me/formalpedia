-- Prove2me | Theorems.Thm_ChanPangGQVI_Contraction_proj_translate
-- name    : ChanPangGQVI.Contraction.proj_translate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:03:36.602059+00:00
-- url     : https://prove2.me/theorems/c3ba4a57-7b9f-470a-a55a-dcc8bfa51a45
-- title:
--   Projection onto a translate: $P_{K(x)}(y)=m(x)+P_{\tilde K}(y-m(x))$ for $K(x)=m(x)+\tilde K$
-- statement:
--   Let $\tilde K\subseteq\mathbb R^n$ be a nonempty closed convex set, let $m:\mathbb R^n\to\mathbb R^n$ be any mapping, and put $K(x)=m(x)+\tilde K$. Write $P_S(z)$ for the projection (Euclidean nearest point) of $z$ on $S$. Then for any vectors $x$ and $y$,
--
--   $$
--   P_{K(x)}(y)=m(x)+P_{\tilde K}\bigl(y-m(x)\bigr).
--   $$
--
--   Projecting on a translated set is the same as translating back, projecting on $\tilde K$ and translating again. This reduces the Lipschitz analysis of $F_\lambda$ to that of the single projection $P_{\tilde K}$.
--
--   **Formalization Note** The hypotheses on $\tilde K$ (nonempty, closed, convex) are the standing hypotheses of Theorem 5.3, under which the display is stated in the paper; they guarantee that both projections are the unique nearest points. No hypothesis on $m$ is needed.
-- source:
--   Chan and Pang, The generalized quasi-variational inequality problem, Math. Oper. Res. 7 (1982), p. 221, §5, proof of Theorem 5.3, first display

import Mathlib
import Definitions.Def_ChanPangGQVI_Shared_Projection
import Definitions.Def_ChanPangGQVI_Contraction_ProjectionMap

namespace ChanPangGQVI.Contraction

/-- Chan and Pang 1982, §5, proof of Theorem 5.3, first display (p. 221): for
`K(x) = m(x) + K̃` with `K̃` a nonempty closed convex set (the standing hypothesis of
Theorem 5.3) and any point-to-point `m`, for any vectors `x` and `y`,
`P_{K(x)}(y) = m(x) + P_{K̃}(y - m(x))`. -/
theorem proj_translate {n : ℕ}
    (m : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (Ktil : Set (EuclideanSpace ℝ (Fin n)))
    (hK_ne : Ktil.Nonempty) (hK_closed : IsClosed Ktil) (hK_convex : Convex ℝ Ktil)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ChanPangGQVI.Shared.proj (Kmap m Ktil x) y =
      m x + ChanPangGQVI.Shared.proj Ktil (y - m x) := by sorry

end ChanPangGQVI.Contraction
