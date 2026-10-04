-- Prove2me | Theorems.Thm_AronszajnRK_Product_direct_product_kernel
-- name    : AronszajnRK.Product.direct_product_kernel
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:50:37.059679+00:00
-- url     : https://prove2.me/theorems/7d28ba24-5f83-419d-aee0-c228de6063f3
-- title:
--   §8, Theorem I — the direct product has kernel $K_1(x_1,y_1)K_2(x_2,y_2)$
-- statement:
--   Let $F_1$, $F_2$ be classes of complex-valued functions on a set $E$ with reproducing kernels $K_1$, $K_2$. The direct product $F' = F_1 \otimes F_2$, a class of functions on $E \times E$, exists, and it possesses the reproducing kernel
--
--   $$
--   K'(x_1, x_2, y_1, y_2) = K_1(x_1, y_1)\, K_2(x_2, y_2).
--   $$
--
--   Restricting $K'$ to the diagonal of $E \times E$ gives the product kernel $K_1 K_2$ treated in §8, Theorem II.
--
--   **Formalization Note** The direct product is the predicate `IsDirectProduct` (elementary products, scalar product, density), not a space defined through its kernel; the statement asserts that some space satisfies it and that every space satisfying it has kernel $K'$.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 361, §8, Theorem I

import Mathlib
import Definitions.Def_AronszajnRK_Product_kernelFn
import Definitions.Def_AronszajnRK_Product_IsDirectProduct

namespace AronszajnRK.Product

universe u v w z

/-- N. Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §8,
Theorem I, p. 361 (PDF p. 25). Let `H₁`, `H₂` be complex RKHSs of functions on `X` with
reproducing kernels `K₁`, `K₂`. The direct product `F′ = F₁ ⊗ F₂` (an RKHS on `X × X`, see
`IsDirectProduct`) exists, and it possesses the reproducing kernel
`K′(x₁, x₂, y₁, y₂) = K₁(x₁, y₁) K₂(x₂, y₂)`. -/
theorem direct_product_kernel {X : Type u} (H₁ : Type v) [NormedAddCommGroup H₁]
    [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [RKHS ℂ H₁ X ℂ] (H₂ : Type w)
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] [RKHS ℂ H₂ X ℂ] :
    (∃ (H' : Type u) (_ : NormedAddCommGroup H') (_ : InnerProductSpace ℂ H')
        (_ : CompleteSpace H') (_ : RKHS ℂ H' (X × X) ℂ), IsDirectProduct H₁ H₂ H') ∧
    ∀ (H' : Type z) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
        [RKHS ℂ H' (X × X) ℂ], IsDirectProduct H₁ H₂ H' →
      ∀ x₁ x₂ y₁ y₂ : X,
        kernelFn H' (x₁, x₂) (y₁, y₂) = kernelFn H₁ x₁ y₁ * kernelFn H₂ x₂ y₂ := by sorry

end AronszajnRK.Product
