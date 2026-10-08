-- Prove2me | Theorems.Thm_ConicQuadIPM_NTScaling_rot_hat_quantities
-- name    : ConicQuadIPM.NTScaling.rot_hat_quantities
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:10:00.097318+00:00
-- url     : https://prove2.me/theorems/018dc17c-6637-40ec-b251-1b620d80d0ef
-- title:
--   Appendix, proof of Lemma 4.2, p. 39 — for the rotated cone, x̂ = Tx, ŝ = Ts are interior to K^q, TQT = Q^q, θ̂ = θ, ŵ = Tw
-- statement:
--   Let $d\ge2$, let $T$, $Q$ be the matrices (18), (19) of the rotated quadratic cone, and let $Q^q = \operatorname{diag}(1,-1,\dots,-1)$ be that of the quadratic cone. Let $x,s\in\operatorname{int}(K^r)$ and $\hat x = Tx$, $\hat s = Ts$. Then
--   1. $\hat x,\hat s\in\operatorname{int}(K^q)$;
--   2. $TQT = Q^q$;
--   3. $\hat\theta = \theta$, where $\hat\theta$ is (30) computed for $\hat x,\hat s$ in $K^q$ and $\theta$ is (30) for $x,s$ in $K^r$;
--   4. $\hat w = Tw$, where $\hat w$ is (32) computed for $\hat x,\hat s$ in $K^q$ and $w$ is (32) for $x,s$ in $K^r$:
--   $$\frac{\hat\theta^{-1}\hat s + \hat\theta Q^q\hat x}{\sqrt2\sqrt{\hat x^T\hat s + \sqrt{\hat x^TQ^q\hat x\;\hat s^TQ^q\hat s}}} = T\,\frac{\theta^{-1}s + \theta Qx}{\sqrt2\sqrt{x^Ts + \sqrt{x^TQx\;s^TQs}}}.$$
--
--   This reduces the NT scaling of the rotated cone to that of the quadratic cone.
--
--   **Formalization Note** Vectors are `Fin d → ℝ` with 0-based indices (the paper's $x_1$ is `coord x 0`); $\|x_{2:n}\|^2$ is `tailSq x 1`, a sum of squares (Euclidean, never Mathlib's sup norm); $x^Ts$ is `x ⬝ᵥ s`. The interior $\operatorname{int}(K)$ is written with strict inequalities ($x_1 > \|x_{2:n}\|$; $2x_1x_2 > \|x_{3:n}\|^2$, $x_1,x_2>0$; $x_1>0$). The page defines $\hat Q := TQT$ and evaluates $\hat\theta$ and $\hat w$ with it; item 2 records that $\hat Q$ is the quadratic-cone matrix, which is what licenses using (31) for $\hat W$.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003), DOI 10.1007/s10107-002-0349-3; authors' preprint of 18 Dec 2000, p. 39, Appendix, proof of Lemma 4.2 (rotated cone)

import Mathlib
import Definitions.Def_ConicQuadIPM_NTScaling_Setting
import Definitions.Def_ConicQuadIPM_NTScaling_Scaling
open Matrix

namespace ConicQuadIPM.NTScaling

/-- Appendix, proof of Lemma 4.2, p. 39 (rotated quadratic cone): with `x̂ = Tx`, `ŝ = Ts`,
`x̂, ŝ ∈ int(K^q)`, `Q̂ = TQT` is the quadratic-cone `Q`, `θ̂ = θ` and `ŵ = Tw`. -/
theorem rot_hat_quantities (d : ℕ) (hd : 2 ≤ d) (x s : Fin d → ℝ)
    (hx : inConeInt .rot x) (hs : inConeInt .rot s) :
    inConeInt .quad (Tmat .rot d *ᵥ x) ∧ inConeInt .quad (Tmat .rot d *ᵥ s) ∧
    Tmat .rot d * Qmat .rot d * Tmat .rot d = Qmat .quad d ∧
    thetaNT .quad d (Tmat .rot d *ᵥ x) (Tmat .rot d *ᵥ s) = thetaNT .rot d x s ∧
    wNT .quad d (Tmat .rot d *ᵥ x) (Tmat .rot d *ᵥ s) = Tmat .rot d *ᵥ wNT .rot d x s := by sorry
end ConicQuadIPM.NTScaling
