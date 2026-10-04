-- Prove2me | Theorems.Thm_AronszajnRK_Product_series_representation
-- name    : AronszajnRK.Product.series_representation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:50:20.127908+00:00
-- url     : https://prove2.me/theorems/8110e990-07e3-4bc5-a175-28d33c6016ff
-- title:
--   §8, Remark — minimal series representation $f=\sum_k f_2^{(k)} g_1^{(k)}$
-- statement:
--   Let $F_1$, $F_2$ be classes of complex-valued functions on a set $E$ with reproducing kernels $K_1$, $K_2$, let $F$ be the class with reproducing kernel $K = K_1 K_2$, and let $\{g_1^{(k)}\}$ be a complete orthonormal system in $F_1$. Every $f \in F$ is representable as a series
--
--   $$
--   f(x) = \sum_{k} f_2^{(k)}(x)\, g_1^{(k)}(x), \qquad f_2^{(k)} \in F_2, \qquad \sum_k \|f_2^{(k)}\|_2^2 < \infty .
--   $$
--
--   Among all such representations there is exactly one that minimizes $\sum_k \|f_2^{(k)}\|_2^2$, and this minimum equals $\|f\|^2$.
--
--   It describes the class $F$ of the product kernel directly in terms of $F_2$ and a basis of $F_1$.
--
--   **Formalization Note** The complete orthonormal system is a Mathlib `HilbertBasis` over an arbitrary index set (the paper writes a sequence); the series converges unconditionally at every point $x$. The minimum is of the squared norms, as on the page.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), pp. 361–362, §8, Remark

import Mathlib
import Definitions.Def_AronszajnRK_Product_kernelFn

namespace AronszajnRK.Product

universe u v w t s

/-- N. Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §8,
Remark, pp. 361–362 (PDF pp. 25–26). Let `H₁`, `H₂` be complex RKHSs on `X` with kernels `K₁`,
`K₂`, let `H` be the RKHS with kernel `K = K₁ K₂` (the class `F` of §8, Theorem II), and let
`(g₁⁽ᵏ⁾)` be a complete orthonormal system in `H₁`. Every `f ∈ F` is representable as a series
`f(x) = Σₖ f₂⁽ᵏ⁾(x) g₁⁽ᵏ⁾(x)` with `f₂⁽ᵏ⁾ ∈ F₂`, `Σₖ ‖f₂⁽ᵏ⁾‖₂² < ∞`; among all such
representations exactly one gives its minimum to `Σₖ ‖f₂⁽ᵏ⁾‖₂²`, and this minimum is `‖f‖²`.
The complete orthonormal system is a Mathlib `HilbertBasis` with an arbitrary index type, and
the series converges (unconditionally) at every point `x`. -/
theorem series_representation {X : Type u} (H₁ : Type v) [NormedAddCommGroup H₁]
    [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [RKHS ℂ H₁ X ℂ] (H₂ : Type w)
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] [RKHS ℂ H₂ X ℂ]
    (H : Type t) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [RKHS ℂ H X ℂ] (hK : ∀ x y : X, kernelFn H x y = kernelFn H₁ x y * kernelFn H₂ x y)
    {ι : Type s} (b : HilbertBasis ι ℂ H₁) (f : H) :
    (∃! c : ι → H₂,
      (Summable (fun k => ‖c k‖ ^ 2) ∧ ∀ x : X, HasSum (fun k => c k x * b k x) (f x)) ∧
      ∀ d : ι → H₂,
        (Summable (fun k => ‖d k‖ ^ 2) ∧ ∀ x : X, HasSum (fun k => d k x * b k x) (f x)) →
        ∑' k, ‖c k‖ ^ 2 ≤ ∑' k, ‖d k‖ ^ 2) ∧
    IsLeast {r : ℝ | ∃ d : ι → H₂, (Summable (fun k => ‖d k‖ ^ 2) ∧
        ∀ x : X, HasSum (fun k => d k x * b k x) (f x)) ∧ r = ∑' k, ‖d k‖ ^ 2} (‖f‖ ^ 2) := by sorry

end AronszajnRK.Product
