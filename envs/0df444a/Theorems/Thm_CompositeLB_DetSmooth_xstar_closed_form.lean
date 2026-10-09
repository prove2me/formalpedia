-- Prove2me | Theorems.Thm_CompositeLB_DetSmooth_xstar_closed_form
-- name    : CompositeLB.DetSmooth.xstar_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:31:51.049011+00:00
-- url     : https://prove2.me/theorems/28985d19-c8d8-4e81-ba36-68bd8d302a12
-- title:
--   Appendix B.3, pp. 14–15 — explicit minimizer and minimum of F^t
-- statement:
--   For $m\ge2$, $1\le t\le k+1$, and orthonormal $v_0,\ldots,v_k$, let $x_t^*=a\sum_{r=0}^{t-1}(1-(r+1)/(t+1))v_r$. This point minimizes $F^t$ over the entire Euclidean space, and
--
--   $$F^t(x_t^*)=-\frac{a^2\lfloor m/2\rfloor}{8m}\left(1-\frac1{t+1}\right).$$
--
--   This is the value comparison used to obtain the explicit optimization gap. The quadratic ignores directions orthogonal to its displayed span, so the theorem asserts that $x_t^*$ is a minimizer, without claiming uniqueness.
-- source:
--   Woodworth & Srebro, arXiv:1605.08003v3, Appendix B.3, p. 14, final display, and p. 15, first two displays

import Mathlib
import Definitions.Def_CompositeLB_DetSmooth_Construction

namespace CompositeLB.DetSmooth

/-- Appendix B.3, pp. 14–15: `xstarT` minimizes the quadratic `F^t` and has
the displayed minimum value. Orthogonal directions make minimizers nonunique. -/
theorem xstar_closed_form {m d k : ℕ} (a : ℝ) (v : ℕ → CompositeLB.DetLip.E d)
    (t : ℕ) (hm : 2 ≤ m) (ht : 1 ≤ t) (htk : t ≤ k + 1)
    (hv : Orthonormal ℝ (fun r : Fin (k + 1) => v (r : ℕ))) :
    (∀ y : CompositeLB.DetLip.E d, Fsum m a v t (xstarT a v t) ≤ Fsum m a v t y) ∧
    Fsum m a v t (xstarT a v t) =
      -(a ^ 2 * ((m / 2 : ℕ) : ℝ) / (8 * (m : ℝ))) *
        (1 - 1 / ((t : ℝ) + 1)) := by sorry

end CompositeLB.DetSmooth
