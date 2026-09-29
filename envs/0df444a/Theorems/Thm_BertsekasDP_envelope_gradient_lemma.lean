-- Prove2me | Theorems.Thm_BertsekasDP_envelope_gradient_lemma
-- name    : BertsekasDP.envelope_gradient_lemma
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-07T15:47:58.451756+00:00
-- url     : https://prove2.me/theorems/a755b8bb-b542-495e-9e23-99fc514729f9
-- title:
--   The envelope lemma (Lemma 3.3.1)
-- statement:
--   **Lemma 3.3.1 (envelope lemma).** Let $F(y,u)$ be continuously differentiable in both arguments, let $U \subseteq \mathbb{R}^m$ be convex, and let $\mu^*$ be a continuously differentiable selection of minimizers: $\mu^*(y) \in U$ and $F(y,\mu^*(y)) \le F(y,u)$ for all $u \in U$ and all $y$. Then the gradient of the minimum value is obtained by differentiating with the minimizer held fixed:
--
--   $$\nabla_y \Bigl[\, F\bigl(y, \mu^*(y)\bigr) \Bigr] \;=\; \nabla_y \Bigl[\, F(y, \bar u) \Bigr]_{\bar u \,=\, \mu^*(y)} \qquad \text{for every } y .$$
--
--   In other words, the indirect term that the chain rule would contribute through $\nabla \mu^*$ vanishes.
--
--   The reason is first-order optimality over the convex set $U$: the derivative of $F$ in the control directions is orthogonal to every feasible variation of the minimizer. This is the step that lets the source differentiate the HJB equation along an optimal trajectory while ignoring the derivatives of the minimizing control law — the passage from the HJB equation to the adjoint equation of the Minimum Principle. The lemma is standard envelope-theorem material and is reusable well beyond control theory, in comparative statics and in duality arguments.
--
--   **Formalization Note** Gradients are Mathlib's, which return the zero vector at points of non-differentiability; here both composite maps are genuinely $C^1$, so they are the classical gradients. Uniqueness of the minimizer is not assumed — only that $\mu^*$ selects one at each $y$ — and no compactness, boundedness or interiority is required.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Lemma 3.3.1

import Mathlib

namespace BertsekasDP

theorem envelope_gradient_lemma {d m : ℕ}
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin m)))
    (hU : Convex ℝ U)
    (hF : ContDiff ℝ 1 (Function.uncurry F))
    (μstar : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m))
    (hμ : ContDiff ℝ 1 μstar)
    (hmem : ∀ y, μstar y ∈ U)
    (hmin : ∀ y, IsMinOn (F y) U (μstar y)) :
    ∀ y, gradient (fun z => F z (μstar z)) y =
      gradient (fun z => F z (μstar y)) y := by sorry

end BertsekasDP
