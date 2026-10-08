-- Prove2me | Theorems.Thm_ConicQuadIPM_NTScaling_rot_scaling_conjugate
-- name    : ConicQuadIPM.NTScaling.rot_scaling_conjugate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:10:11.150978+00:00
-- url     : https://prove2.me/theorems/c2a52627-3e3a-4396-b000-c3ed93ed8bcc
-- title:
--   Appendix, proof of Lemma 4.2, p. 40 — T(−Q + (Te₁+w)(Te₁+w)ᵀ/(1+e₁ᵀTw))T is (31) at ŵ = Tw
-- statement:
--   Let $d\ge2$, let $T$, $Q$ be the matrices (18), (19) of the rotated quadratic cone and $Q^q=\operatorname{diag}(1,-1,\dots,-1)$. For every $w\in\mathbb R^d$,
--   $$T\Bigl(-Q + \frac{(Te_1+w)(Te_1+w)^T}{1+e_1^TTw}\Bigr)T = -Q^q + \frac{(e_1+\hat w)(e_1+\hat w)^T}{1+e_1^T\hat w},\qquad \hat w = Tw.$$
--
--   Combined with (63) this shows that the rotated-cone matrix (34) is the conjugate by $T$ of the quadratic-cone NT matrix (31), from which (34) follows.
--
--   **Formalization Note** Vectors are `Fin d → ℝ` with 0-based indices (the paper's $x_1$ is `coord x 0`); $\|x_{2:n}\|^2$ is `tailSq x 1`, a sum of squares (Euclidean, never Mathlib's sup norm); $x^Ts$ is `x ⬝ᵥ s`. The page writes the denominator as $1+\hat w^i$, a printed slip for $1+(e_1)^T\hat w^i = 1 + \hat w^i_1$; the Lean uses $1+e_1^T\hat w$. Both sides use Mathlib's total inverse, so the identity is stated for every $w$.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003), DOI 10.1007/s10107-002-0349-3; authors' preprint of 18 Dec 2000, p. 40, Appendix, proof of Lemma 4.2 (end)

import Mathlib
import Definitions.Def_ConicQuadIPM_NTScaling_Setting
import Definitions.Def_ConicQuadIPM_NTScaling_Scaling
open Matrix

namespace ConicQuadIPM.NTScaling

/-- Appendix, proof of Lemma 4.2, p. 40 (rotated quadratic cone): conjugating the matrix (34)
by `T` gives the quadratic-cone matrix (31) at `ŵ = Tw`, i.e. `T W T = Ŵ`. -/
theorem rot_scaling_conjugate (d : ℕ) (hd : 2 ≤ d) (w : Fin d → ℝ) :
    Tmat .rot d * Wrot d w * Tmat .rot d = WquadOuter d (Tmat .rot d *ᵥ w) := by sorry
end ConicQuadIPM.NTScaling
