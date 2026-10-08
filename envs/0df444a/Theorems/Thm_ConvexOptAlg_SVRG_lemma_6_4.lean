-- Prove2me | Theorems.Thm_ConvexOptAlg_SVRG_lemma_6_4
-- name    : ConvexOptAlg.SVRG.lemma_6_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T18:44:52.851418+00:00
-- url     : https://prove2.me/theorems/0d1e7fcc-8208-4ccf-b466-c8af330ea736
-- title:
--   Lemma 6.4, p. 336 — component-gradient second moment
-- statement:
--   Let $m\ge1$, let each $f_i:\mathbb R^n\to\mathbb R$ be convex and differentiable with $\beta$-Lipschitz gradient $g_i$, where $\beta>0$, and put $f=m^{-1}\sum_i f_i$. If $x^*$ minimizes $f$ over $\mathbb R^n$, then for every $x$ and a uniform component index $I\in[m]$,
--
--   $$\mathbb E_I\|g_I(x)-g_I(x^*)\|_2^2\le 2\beta\bigl(f(x)-f(x^*)\bigr).$$
--
--   This bounds the component-gradient difference by the objective gap and supplies the variance estimate used in the SVRG analysis.
--
--   **Formalization Note** The standing convention of the book supplies the minimizer $x^*$; the positive smoothness constant and nonempty component family make the displayed average well-defined.
-- source:
--   Bubeck, arXiv:1405.4980v2, Lemma 6.4, p. 336, PDF p. 109

import Mathlib
import Definitions.Def_ConvexOptAlg_SVRG_Defs

open scoped InnerProductSpace

namespace ConvexOptAlg.SVRG

/-- Lemma 6.4, p. 336. The mean squared difference of component gradients
at `x` and a minimizer `xstar` is bounded by twice `β` times the objective gap. -/
theorem lemma_6_4 {n m : ℕ}
    (fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (β : ℝ) (x xstar : EuclideanSpace ℝ (Fin n))
    (hm : 0 < m) (hβ : 0 < β) (hfamily : SmoothConvexFamily fs gs β)
    (hmin : ∀ z, objective fs xstar ≤ objective fs z) :
    uniformMean (fun i : Fin m => ‖gs i x - gs i xstar‖ ^ 2) ≤
      2 * β * (objective fs x - objective fs xstar) := by sorry

end ConvexOptAlg.SVRG
