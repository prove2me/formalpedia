-- Prove2me | Theorems.Thm_CompoundSMM_Conv_drop_proximal_term
-- name    : CompoundSMM.Conv.drop_proximal_term
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:52:41.045281+00:00
-- url     : https://prove2.me/theorems/d230a241-f978-4db4-ae45-6c6aa278053e
-- title:
--   Proof of Theorem 5, after (15), p. 14 — V convex on X and V(x^∞) ≤ V(x) + ‖x − x^∞‖²/(2ρ) on X imply x^∞ ∈ argmin_X V
-- statement:
--   Let $X\subseteq\mathbb R^n$ be convex, $V:\mathbb R^n\to\mathbb R$ convex on $X$, $x^\infty\in X$ and $\rho>0$. If
--
--   $$V(x^\infty)\ \le\ V(x)+\frac1{2\rho}\|x-x^\infty\|^2\qquad\text{for all }x\in X,$$
--
--   then $V(x^\infty)\le V(x)$ for all $x\in X$, i.e. $x^\infty\in\operatorname{argmin}_{x\in X}V(x)$.
--
--   This is the last step of the proof of Theorem 5: applied to $V=\widehat V_\infty(\bullet;x^\infty)$ and inequality (15), it removes the proximal term and yields the theorem's conclusion.
-- source:
--   Liu, Cui & Pang, Solving nonsmooth and nonconvex compound stochastic programs with applications to risk measure minimization, arXiv:2004.14342v3, p. 14, proof of Theorem 5, (15) and the sentence following it

import Mathlib
import Definitions.Def_CompoundSMM_Conv_Setting

namespace CompoundSMM.Conv

/-- Proof of Theorem 5, after (15), p. 14: if `V` is convex on the convex set `X`, `xinf ∈ X`,
`ρ > 0` and `V(xinf) ≤ V(x) + ‖x − xinf‖²/(2ρ)` for all `x ∈ X`, then `xinf` minimizes `V`
over `X`. -/
theorem drop_proximal_term {n : ℕ} (X : Set (E n)) (hX : Convex ℝ X) (V : E n → ℝ)
    (hV : ConvexOn ℝ X V) (xinf : E n) (hxinf : xinf ∈ X) (ρ : ℝ) (hρ : 0 < ρ)
    (h15 : ∀ x ∈ X, V xinf ≤ V x + ‖x - xinf‖ ^ 2 / (2 * ρ)) :
    IsMinOn V X xinf := by sorry

end CompoundSMM.Conv
