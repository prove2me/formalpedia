-- Prove2me | Theorems.Thm_ConicQuadIPM_NTScaling_denominator_pos
-- name    : ConicQuadIPM.NTScaling.denominator_pos
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:10:09.213369+00:00
-- url     : https://prove2.me/theorems/7e63c6aa-1c2b-4cc3-8bb4-b2877b4cbde8
-- title:
--   Appendix, proof of Lemma 4.2, p. 39 — xᵀs + √(xᵀQx · sᵀQs) > 0 for interior x, s
-- statement:
--   Let $K$ be one of $\mathbb R_+$, $K^q$, $K^r$ with matrix $Q$, and let $x, s\in\operatorname{int}(K)$. Then
--   $$x^Ts + \sqrt{x^TQx\; s^TQs} > 0.$$
--
--   The quantity is the radicand in the denominator of (32), so this makes the vector $w$ of Lemma 4.2 well defined.
--
--   **Formalization Note** The statement is made for one cone block $K^i$, with the superscript $i$ dropped: $\Theta$ and $W$ are block diagonal (p. 11–12), so the per-block statement is the paper's statement block by block. Vectors are `Fin d → ℝ` with 0-based indices (the paper's $x_1$ is `coord x 0`); $\|x_{2:n}\|^2$ is `tailSq x 1`, a sum of squares (Euclidean, never Mathlib's sup norm); $x^Ts$ is `x ⬝ᵥ s`. The dimension conventions the paper leaves implicit ($d=1$ for $\mathbb R_+$, $d\ge 1$ for $K^q$, $d\ge2$ for $K^r$) are the hypothesis `WellFormedBlock kind d`. The interior $\operatorname{int}(K)$ is written with strict inequalities ($x_1 > \|x_{2:n}\|$; $2x_1x_2 > \|x_{3:n}\|^2$, $x_1,x_2>0$; $x_1>0$). The page states the claim for the quadratic cone (and writes $\operatorname{int}(K)^i$ for $\operatorname{int}(K^i)$); it holds, and is stated here, for each of the three cone kinds, since (32) is used for the rotated cone too.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003), DOI 10.1007/s10107-002-0349-3; authors' preprint of 18 Dec 2000, p. 39, Appendix, proof of Lemma 4.2

import Mathlib
import Definitions.Def_ConicQuadIPM_NTScaling_Setting
import Definitions.Def_ConicQuadIPM_NTScaling_Scaling
open Matrix

namespace ConicQuadIPM.NTScaling

/-- Appendix, proof of Lemma 4.2, p. 39: `xᵀs + √(xᵀQx · sᵀQs) > 0` for interior `x, s`
(stated on the page for the quadratic cone; here for each of the three cone kinds). -/
theorem denominator_pos (kind : ConicQuadIPM.Complementarity.ConeKind) (d : ℕ) (hwf : WellFormedBlock kind d)
    (x s : Fin d → ℝ) (hx : inConeInt kind x) (hs : inConeInt kind s) :
    0 < x ⬝ᵥ s + Real.sqrt ((x ⬝ᵥ (Qmat kind d *ᵥ x)) * (s ⬝ᵥ (Qmat kind d *ᵥ s))) := by sorry
end ConicQuadIPM.NTScaling
