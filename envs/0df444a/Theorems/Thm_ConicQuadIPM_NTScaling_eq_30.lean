-- Prove2me | Theorems.Thm_ConicQuadIPM_NTScaling_eq_30
-- name    : ConicQuadIPM.NTScaling.eq_30
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:09:51.743978+00:00
-- url     : https://prove2.me/theorems/5cf228bb-e62d-4456-a8cb-9a759d07b468
-- title:
--   (30), p. 15 — every NT scaling of interior points has θ² = √(sᵀQs / xᵀQx)
-- statement:
--   Let $K$ be one of $\mathbb R_+$, $K^q$, $K^r$ with matrix $Q$, and let $x,s\in\operatorname{int}(K)$. If $\theta>0$ and the scaling matrix $W$ form a Nesterov–Todd scaling of $(x,s)$, i.e. $\theta W x = (\theta W)^{-1}s$ (28), then
--   $$\theta^2 = \sqrt{\frac{s^TQs}{x^TQx}}.\qquad(30)$$
--
--   This is the first assertion of Lemma 4.2: the scalar part of an NT scaling is determined by $x$ and $s$ alone.
--
--   **Formalization Note** The statement is made for one cone block $K^i$, with the superscript $i$ dropped: $\Theta$ and $W$ are block diagonal (p. 11–12), so the per-block statement is the paper's statement block by block. Vectors are `Fin d → ℝ` with 0-based indices (the paper's $x_1$ is `coord x 0`); $\|x_{2:n}\|^2$ is `tailSq x 1`, a sum of squares (Euclidean, never Mathlib's sup norm); $x^Ts$ is `x ⬝ᵥ s`. The dimension conventions the paper leaves implicit ($d=1$ for $\mathbb R_+$, $d\ge 1$ for $K^q$, $d\ge2$ for $K^r$) are the hypothesis `WellFormedBlock kind d`. The interior $\operatorname{int}(K)$ is written with strict inequalities ($x_1 > \|x_{2:n}\|$; $2x_1x_2 > \|x_{3:n}\|^2$, $x_1,x_2>0$; $x_1>0$). The lemma names $\theta$ without quantifying it; here it is read as "for every NT scaling", which is how the Appendix proves it (from Lemma 3.3).
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003), DOI 10.1007/s10107-002-0349-3; authors' preprint of 18 Dec 2000, p. 15, Lemma 4.2 (30); proof: Appendix, proof of Lemma 4.2, p. 38

import Mathlib
import Definitions.Def_ConicQuadIPM_NTScaling_Setting
import Definitions.Def_ConicQuadIPM_NTScaling_Scaling
open Matrix

namespace ConicQuadIPM.NTScaling

/-- (30), p. 15, with the Appendix proof of Lemma 4.2, p. 38: every NT scaling of interior points
has `θ² = √(sᵀQs / xᵀQx)`. -/
theorem eq_30 (kind : ConicQuadIPM.Complementarity.ConeKind) (d : ℕ) (hwf : WellFormedBlock kind d)
    (x s : Fin d → ℝ) (hx : inConeInt kind x) (hs : inConeInt kind s)
    (θ : ℝ) (W : Matrix (Fin d) (Fin d) ℝ) (hNT : IsNT kind d θ W x s) :
    θ ^ 2 = Real.sqrt ((s ⬝ᵥ (Qmat kind d *ᵥ s)) / (x ⬝ᵥ (Qmat kind d *ᵥ x))) := by sorry
end ConicQuadIPM.NTScaling
