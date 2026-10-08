-- Prove2me | Theorems.Thm_ConicQuadIPM_NTScaling_lemma_4_2
-- name    : ConicQuadIPM.NTScaling.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:09:55.574878+00:00
-- url     : https://prove2.me/theorems/9e1f90e5-723d-4069-a311-a5d65bf15266
-- title:
--   Lemma 4.2, p. 15 — the NT scaling: θ² = √(sᵀQs/xᵀQx), and W is (1/θ)(X⁻¹S)^{1/2}, (31) or (34) with w of (32), W² = −Q + 2wwᵀ
-- statement:
--   Let $K$ be one cone block — the positive half-line $\mathbb R_+$, the quadratic cone $K^q$ or the rotated quadratic cone $K^r$ — with matrices $T$, $Q$ of Definition 3.2, and let $x,s\in\operatorname{int}(K)$. A **Nesterov–Todd (NT) scaling** of $(x,s)$ is a pair $\theta>0$, $W$ with $W\succ0$, $WQW=Q$ and $\theta Wx = (\theta W)^{-1}s$ (28). Then:
--
--   1. **(30)** Every NT scaling satisfies
--   $$\theta^2 = \sqrt{\frac{s^TQs}{x^TQx}}.$$
--   2. Let $\theta$ be given by (30) and
--   $$w = \frac{\theta^{-1}s + \theta Qx}{\sqrt2\sqrt{x^Ts + \sqrt{x^TQx\;s^TQs}}}.\qquad(32)$$
--      - i) If $K = \mathbb R_+$, then $W = \frac1\theta\bigl(X^{-1}S\bigr)^{1/2}$ (with $X = \operatorname{mat}(Tx)$, $S=\operatorname{mat}(Ts)$) makes $(\theta,W)$ an NT scaling.
--      - ii) If $K = K^q$, then
--   $$W = \begin{bmatrix} w_1 & w_{2:d}^T\\ w_{2:d} & I + \frac{w_{2:d}w_{2:d}^T}{1+w_1}\end{bmatrix} = -Q + \frac{(e_1+w)(e_1+w)^T}{1+e_1^Tw}\qquad(31)$$
--        makes $(\theta,W)$ an NT scaling, the two expressions agree, and $W^2 = -Q + 2ww^T$ (33).
--      - iii) If $K = K^r$, then
--   $$W = -Q + \frac{(Te_1+w)(Te_1+w)^T}{1+e_1^TTw}\qquad(34)$$
--        makes $(\theta,W)$ an NT scaling, and $W^2 = -Q + 2ww^T$ (35).
--
--   The lemma gives closed forms for the NT scaling of each cone of a conic quadratic program: $W$ is determined by one vector $w$ per cone, and $W$, $W^2$ and their inverses can be applied in $O(n)$ operations. This is what makes the NT direction practical in an implementation such as MOSEK.
--
--   **Formalization Note** The statement is made for one cone block $K^i$, with the superscript $i$ dropped: $\Theta$ and $W$ are block diagonal (p. 11–12), so the per-block statement is the paper's statement block by block. Vectors are `Fin d → ℝ` with 0-based indices (the paper's $x_1$ is `coord x 0`); $\|x_{2:n}\|^2$ is `tailSq x 1`, a sum of squares (Euclidean, never Mathlib's sup norm); $x^Ts$ is `x ⬝ᵥ s`. The dimension conventions the paper leaves implicit ($d=1$ for $\mathbb R_+$, $d\ge 1$ for $K^q$, $d\ge2$ for $K^r$) are the hypothesis `WellFormedBlock kind d`. The interior $\operatorname{int}(K)$ is written with strict inequalities ($x_1 > \|x_{2:n}\|$; $2x_1x_2 > \|x_{3:n}\|^2$, $x_1,x_2>0$; $x_1>0$). The paper names $\theta$ and $W$ without quantifying them. The statement reads them as in the paper's proof: part 1 holds for every NT scaling, and part 2 asserts that the displayed $\theta$, $W$ form an NT scaling. Uniqueness of the NT scaling among all scaling matrices is not claimed (the paper does not prove it). For $\mathbb R_+$, $X^{-1}S$ is the $1\times1$ matrix $s_1/x_1$ and its square root is $\sqrt{s_1/x_1}$ (`Wnonneg`).
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003), DOI 10.1007/s10107-002-0349-3; authors' preprint of 18 Dec 2000, p. 15, Lemma 4.2 (30)–(35); proof: Appendix, pp. 38–40

import Mathlib
import Definitions.Def_ConicQuadIPM_NTScaling_Setting
import Definitions.Def_ConicQuadIPM_NTScaling_Scaling
open Matrix

namespace ConicQuadIPM.NTScaling

/-- Lemma 4.2, p. 15, for one cone block with `x, s` in the interior:
(a) every NT scaling `θ, W` satisfies (30); (b) `θ` of (30) with `W` of i) (`R₊`), (31) (`K^q`)
or (34) (`K^r`), `w` of (32), is an NT scaling; the two forms of (31) agree; and
`W² = −Q + 2wwᵀ` ((33), (35)). -/
theorem lemma_4_2 (kind : ConicQuadIPM.Complementarity.ConeKind) (d : ℕ) (hwf : WellFormedBlock kind d)
    (x s : Fin d → ℝ) (hx : inConeInt kind x) (hs : inConeInt kind s) :
    (∀ (θ : ℝ) (W : Matrix (Fin d) (Fin d) ℝ), IsNT kind d θ W x s →
        θ ^ 2 = Real.sqrt ((s ⬝ᵥ (Qmat kind d *ᵥ s)) / (x ⬝ᵥ (Qmat kind d *ᵥ x)))) ∧
    (kind = .nonneg →
        IsNT .nonneg d (thetaNT .nonneg d x s) (Wnonneg d x s) x s) ∧
    (kind = .quad →
        IsNT .quad d (thetaNT .quad d x s) (WquadOuter d (wNT .quad d x s)) x s ∧
        WquadArrow (wNT .quad d x s) = WquadOuter d (wNT .quad d x s) ∧
        WquadOuter d (wNT .quad d x s) * WquadOuter d (wNT .quad d x s) =
          -Qmat .quad d + (2 : ℝ) • vecMulVec (wNT .quad d x s) (wNT .quad d x s)) ∧
    (kind = .rot →
        IsNT .rot d (thetaNT .rot d x s) (Wrot d (wNT .rot d x s)) x s ∧
        Wrot d (wNT .rot d x s) * Wrot d (wNT .rot d x s) =
          -Qmat .rot d + (2 : ℝ) • vecMulVec (wNT .rot d x s) (wNT .rot d x s)) := by sorry
end ConicQuadIPM.NTScaling
