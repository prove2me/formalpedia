-- Prove2me | Theorems.Thm_ConicQuadIPM_NTScaling_w_derivation
-- name    : ConicQuadIPM.NTScaling.w_derivation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:09:55.544978+00:00
-- url     : https://prove2.me/theorems/38a1f451-add3-4e50-845d-05779b12999e
-- title:
--   Appendix, proof of Lemma 4.2, pp. 38–39 — from s = θ²(−Q + 2wwᵀ)x: 2θ²(wᵀx)² = xᵀs + √(xᵀQx sᵀQs), and w is (32)
-- statement:
--   Let $d\ge1$, $Q=\operatorname{diag}(1,-1,\dots,-1)$, and let $x,s$ lie in the interior of the quadratic cone $K^q$. Let $\theta>0$ satisfy (30), $\theta^2 = \sqrt{s^TQs/x^TQx}$, and let $w\in\mathbb R^d$ satisfy
--   $$s = \theta^2\bigl(-Q + 2ww^T\bigr)x.$$
--   Then
--   1. $x^Ts = \theta^2\bigl(-x^TQx + 2(w^Tx)^2\bigr)$;
--   2. $2\theta^2(w^Tx)^2 = x^Ts + \sqrt{x^TQx\; s^TQs}$;
--   3. if moreover $w^Tx>0$, then
--   $$w = \frac{\theta^{-1}s + \theta Qx}{\sqrt2\sqrt{x^Ts + \sqrt{x^TQx\; s^TQs}}}.\qquad(32)$$
--
--   This is the derivation of the formula (32) for $w$ from the NT condition (29) combined with (62).
--
--   **Formalization Note** Vectors are `Fin d → ℝ` with 0-based indices (the paper's $x_1$ is `coord x 0`); $\|x_{2:n}\|^2$ is `tailSq x 1`, a sum of squares (Euclidean, never Mathlib's sup norm); $x^Ts$ is `x ⬝ᵥ s`. The interior $\operatorname{int}(K)$ is written with strict inequalities ($x_1 > \|x_{2:n}\|$; $2x_1x_2 > \|x_{3:n}\|^2$, $x_1,x_2>0$; $x_1>0$). The page concludes (32) from item 2 by taking a square root, which silently fixes the sign $w^Tx>0$; item 3 therefore carries $w^Tx>0$ as an explicit, disclosed hypothesis. Items 1 and 2 hold without it.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003), DOI 10.1007/s10107-002-0349-3; authors' preprint of 18 Dec 2000, pp. 38–39, Appendix, proof of Lemma 4.2 (after (62))

import Mathlib
import Definitions.Def_ConicQuadIPM_NTScaling_Setting
import Definitions.Def_ConicQuadIPM_NTScaling_Scaling
open Matrix

namespace ConicQuadIPM.NTScaling

/-- Appendix, proof of Lemma 4.2, pp. 38–39 (quadratic cone): if `θ > 0` satisfies (30) and
`s = θ²(−Q + 2wwᵀ)x`, then `xᵀs = θ²(−xᵀQx + 2(wᵀx)²)`,
`2θ²(wᵀx)² = xᵀs + √(xᵀQx · sᵀQs)`, and, when `wᵀx > 0`, `w` is given by (32). -/
theorem w_derivation (d : ℕ) (hd : 1 ≤ d) (x s : Fin d → ℝ)
    (hx : inConeInt .quad x) (hs : inConeInt .quad s)
    (θ : ℝ) (hθ : 0 < θ)
    (h30 : θ ^ 2 = Real.sqrt ((s ⬝ᵥ (Qmat .quad d *ᵥ s)) / (x ⬝ᵥ (Qmat .quad d *ᵥ x))))
    (w : Fin d → ℝ)
    (h29 : s = θ ^ 2 • ((-Qmat .quad d + (2 : ℝ) • vecMulVec w w) *ᵥ x)) :
    x ⬝ᵥ s = θ ^ 2 * (-(x ⬝ᵥ (Qmat .quad d *ᵥ x)) + 2 * (w ⬝ᵥ x) ^ 2) ∧
    2 * θ ^ 2 * (w ⬝ᵥ x) ^ 2 =
      x ⬝ᵥ s + Real.sqrt ((x ⬝ᵥ (Qmat .quad d *ᵥ x)) * (s ⬝ᵥ (Qmat .quad d *ᵥ s))) ∧
    (0 < w ⬝ᵥ x →
      w = (Real.sqrt 2 *
            Real.sqrt (x ⬝ᵥ s +
              Real.sqrt ((x ⬝ᵥ (Qmat .quad d *ᵥ x)) * (s ⬝ᵥ (Qmat .quad d *ᵥ s)))))⁻¹ •
          (θ⁻¹ • s + θ • (Qmat .quad d *ᵥ x))) := by sorry
end ConicQuadIPM.NTScaling
