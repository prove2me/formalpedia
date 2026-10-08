-- Prove2me | Theorems.Thm_AronszajnRK_Product_product_kernel_theorem
-- name    : AronszajnRK.Product.product_kernel_theorem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T04:50:44.579101+00:00
-- url     : https://prove2.me/theorems/944700a5-ce24-4157-bbf8-6f4d6bf355fa
-- title:
--   §8, Theorem II — $K_1K_2$ is the kernel of the diagonal restrictions of $F_1\otimes F_2$
-- statement:
--   Let $F_1$, $F_2$ be classes of complex-valued functions on a set $E$ with reproducing kernels $K_1$, $K_2$ and norms $\|\cdot\|_1$, $\|\cdot\|_2$, and let $F' = F_1 \otimes F_2$ be their direct product, a class of functions on $E \times E$ with norm $\|\cdot\|'$. Then the kernel
--
--   $$
--   K(x, y) = K_1(x, y)\, K_2(x, y)
--   $$
--
--   is the reproducing kernel of the class $F$ of the restrictions of all functions of $F'$ to the diagonal $\{(x, x) : x \in E\}$, and for any such restriction $f$
--
--   $$
--   \|f\| = \min \{\, \|g'\|' : g' \in F',\ g'(x, x) = f(x) \text{ for all } x \in E \,\},
--   $$
--
--   the minimum being attained.
--
--   This identifies the space belonging to the pointwise product of two reproducing kernels, the product of positive matrices known from Schur's theorem.
--
--   **Formalization Note** The diagonal is identified with $E$ through $x \mapsto (x, x)$, so the restriction of $g'$ is the function $x \mapsto g'(x,x)$. The statement asserts that a reproducing-kernel Hilbert space with kernel $K_1K_2$ exists and that every such space has exactly these functions and this norm. The norm is not squared. The direct product is a hypothesis (`IsDirectProduct`); its existence is §8, Theorem I.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 361, §8, Theorem II

import Mathlib
import Definitions.Def_AronszajnRK_Product_kernelFn
import Definitions.Def_AronszajnRK_Product_IsDirectProduct

namespace AronszajnRK.Product

universe u v w z t

/-- N. Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §8,
Theorem II, p. 361 (PDF p. 25). Let `H₁`, `H₂` be complex RKHSs of functions on `X` with
reproducing kernels `K₁`, `K₂`, and let `H'` be their direct product `F′ = F₁ ⊗ F₂` on
`X × X`. The kernel `K(x, y) = K₁(x, y) K₂(x, y)` is the reproducing kernel of the class `F` of
the restrictions of all functions of `F′` to the diagonal `{(x, x)}` (identified with `X`
through `x ↦ (x, x)`), and for every such restriction `f`, `‖f‖ = min ‖g′‖′` over all
`g′ ∈ F′` whose restriction to the diagonal is `f` (the minimum is attained; the norm is not
squared). Stated as: an RKHS on `X` with kernel `K₁ K₂` exists, and every RKHS on `X` with
kernel `K₁ K₂` has exactly the diagonal restrictions as its functions and that minimum as its
norm. -/
theorem product_kernel_theorem {X : Type u} (H₁ : Type v) [NormedAddCommGroup H₁]
    [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [RKHS ℂ H₁ X ℂ] (H₂ : Type w)
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] [RKHS ℂ H₂ X ℂ]
    (H' : Type z) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    [RKHS ℂ H' (X × X) ℂ] (hH' : IsDirectProduct H₁ H₂ H') :
    (∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (_ : CompleteSpace H) (_ : RKHS ℂ H X ℂ),
        ∀ x y : X, kernelFn H x y = kernelFn H₁ x y * kernelFn H₂ x y) ∧
    ∀ (H : Type t) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        [RKHS ℂ H X ℂ], (∀ x y : X, kernelFn H x y = kernelFn H₁ x y * kernelFn H₂ x y) →
      Set.range (fun f : H => (⇑f : X → ℂ)) = {φ : X → ℂ | ∃ g : H', φ = fun x => g (x, x)} ∧
      ∀ f : H, IsLeast
        {r : ℝ | ∃ g : H', (fun x => g (x, x)) = (⇑f : X → ℂ) ∧ r = ‖g‖} ‖f‖ := by sorry

end AronszajnRK.Product
