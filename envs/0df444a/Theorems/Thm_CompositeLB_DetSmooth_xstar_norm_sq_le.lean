-- Prove2me | Theorems.Thm_CompositeLB_DetSmooth_xstar_norm_sq_le
-- name    : CompositeLB.DetSmooth.xstar_norm_sq_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:31:54.194184+00:00
-- url     : https://prove2.me/theorems/17dff903-0864-4461-93f7-dd10a85c6797
-- title:
--   Appendix B.3, p. 15 — squared norm of the explicit minimizer
-- statement:
--   For $1\le t\le k+1$ and orthonormal $v_0,\ldots,v_k$, the explicit point $x_t^*=a\sum_{r=0}^{t-1}(1-(r+1)/(t+1))v_r$ satisfies
--
--   $$\|x_t^*\|^2=a^2\sum_{r=0}^{t-1}\left(1-\frac{r+1}{t+1}\right)^2\le\frac{a^2t}{3}.$$
--
--   Choosing $a=\sqrt{3/(k+1)}$ therefore places $x_{k+1}^*$ in the unit ball, as required for the bounded-domain lower bound. The paper's subsequent assertion that its norm equals one is a printed slip: the established conclusion is the inequality.
-- source:
--   Woodworth & Srebro, arXiv:1605.08003v3, Appendix B.3, p. 15, norm computation

import Mathlib
import Definitions.Def_CompositeLB_DetSmooth_Construction

namespace CompositeLB.DetSmooth

/-- Appendix B.3, p. 15: the squared norm of the displayed minimizer, with
its finite-sum identity and its `a²t/3` bound. -/
theorem xstar_norm_sq_le {d k : ℕ} (a : ℝ) (v : ℕ → CompositeLB.DetLip.E d)
    (t : ℕ) (ht : 1 ≤ t) (htk : t ≤ k + 1)
    (hv : Orthonormal ℝ (fun r : Fin (k + 1) => v (r : ℕ))) :
    (‖xstarT a v t‖ ^ 2 =
      a ^ 2 * ∑ r ∈ Finset.range t,
        (1 - ((r : ℝ) + 1) / ((t : ℝ) + 1)) ^ 2) ∧
    ‖xstarT a v t‖ ^ 2 ≤ a ^ 2 * (t : ℝ) / 3 := by sorry

end CompositeLB.DetSmooth
