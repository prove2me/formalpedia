-- Prove2me | Theorems.Thm_ConvexOptAlg_CoordDescent_thm_6_8_lemma_6_9_weighted
-- name    : ConvexOptAlg.CoordDescent.thm_6_8_lemma_6_9_weighted
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T19:09:04.364502+00:00
-- url     : https://prove2.me/theorems/3a93e2e6-c3be-4f49-83b4-308ddfcbf82a
-- title:
--   §6.4.2, proof of Theorem 6.8, p. 342 — Lemma 6.9 for ‖·‖_[1−γ]: (‖∇f(x)‖*_[1−γ])² ≥ 2α(f(x) − f(x*))
-- statement:
--   Let $\beta_1,\dots,\beta_n>0$, $\gamma\in\mathbb R$, $\alpha>0$, and let $f:\mathbb R^n\to\mathbb R$ be differentiable and $\alpha$-strongly convex w.r.t. the weighted norm $\|x\|_{[1-\gamma]}=\sqrt{\sum_i\beta_i^{1-\gamma}x_i^2}$, i.e. $f(x)-f(y)\le\nabla f(x)^\top(x-y)-\frac{\alpha}{2}\|x-y\|_{[1-\gamma]}^2$ for all $x,y$. Let $x^*$ minimize $f$. Then for every $x$,
--
--   $$\Big(\|\nabla f(x)\|^*_{[1-\gamma]}\Big)^2\ge2\alpha\big(f(x)-f(x^*)\big),\qquad \|v\|^*_{[1-\gamma]}=\sqrt{\sum_i v_i^2/\beta_i^{1-\gamma}}.$$
--
--   This is Lemma 6.9 for the norm $\|\cdot\|_{[1-\gamma]}$, whose dual norm is $\|\cdot\|^*_{[1-\gamma]}$; the proof of Theorem 6.8 applies it at the iterate $x_s$.
--
--   **Formalization Note** The weighted instance is stated on its own, with the dual norm written out, rather than derived from the general Lemma 6.9, which would need $\|\cdot\|_{[1-\gamma]}$ as a normed-space structure and its dual identified with $\|\cdot\|^*_{[1-\gamma]}$. The book applies it with $\delta_s=\mathbb Ef(x_s)-f(x^*)$; this is the pointwise form at a point $x$. The minimizer is the book's standing assumption.
-- source:
--   Bubeck, arXiv:1405.4980v2, §6.4.2, proof of Theorem 6.8, p. 342 (Lemma 6.9 applied to ‖·‖_[1−γ])

import Mathlib
import Definitions.Def_ConvexOptAlg_CoordDescent_Defs

namespace ConvexOptAlg.CoordDescent

/-- Proof of Theorem 6.8, Lemma 6.9 applied to the weighted norm (Bubeck, arXiv:1405.4980v2, p. 342):
if `f` is α-strongly convex with respect to `‖·‖_[1−γ]` (`α > 0`, `βᵢ > 0`) and `x*` minimizes `f`,
then for every `x`, `(‖∇f(x)‖*_[1−γ])² ≥ 2α (f(x) − f(x*))`. -/
theorem thm_6_8_lemma_6_9_weighted {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : Fin n → ℝ) (γ α : ℝ)
    (hβ : ∀ i, 0 < β i) (hα : 0 < α) (hsc : IsStronglyConvexWNorm f g β (1 - γ) α)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ y, f xstar ≤ f y) (x : EuclideanSpace ℝ (Fin n)) :
    2 * α * (f x - f xstar) ≤ wnormDual β (1 - γ) (g x) ^ 2 := by sorry

end ConvexOptAlg.CoordDescent
