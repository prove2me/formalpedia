-- Prove2me | Theorems.Thm_AronszajnRK_Product_restriction_theorem
-- name    : AronszajnRK.Product.restriction_theorem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T04:50:10.505832+00:00
-- url     : https://prove2.me/theorems/2a9a0192-a58e-4126-9ea8-d6adb67e1703
-- title:
--   §5, Theorem — restriction of a reproducing kernel to a subset
-- statement:
--   Let $K$ be the reproducing kernel of a class $F$ of complex-valued functions on a set $E$ with norm $\|\cdot\|$, and let $E_1 \subseteq E$. Then the restriction of $K$ to $E_1 \times E_1$ is the reproducing kernel of the class $F_1$ of all restrictions $f|_{E_1}$, $f \in F$, and for every $f_1 \in F_1$
--
--   $$
--   \|f_1\|_1 = \min \{\, \|f\| : f \in F,\ f|_{E_1} = f_1 \,\},
--   $$
--
--   the minimum being attained.
--
--   Applied with $E \times E$ and its diagonal, this yields the class and norm belonging to the product kernel in §8, Theorem II.
--
--   **Formalization Note** The statement asserts that a reproducing-kernel Hilbert space on $E_1$ with kernel $K|_{E_1 \times E_1}$ exists, and that every such space has exactly the restrictions as its functions and the attained minimum as its norm (by the uniqueness of the space with a given kernel this is the paper's statement). The norm is not squared.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 351, §5, Theorem

import Mathlib
import Definitions.Def_AronszajnRK_Product_kernelFn

namespace AronszajnRK.Product

universe u v w

/-- N. Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §5,
Theorem, p. 351 (PDF p. 15). If `K` is the reproducing kernel of the class `F` (the RKHS `H`)
of functions on `X`, then `K` restricted to a subset `E₁ ⊆ X` is the reproducing kernel of the
class `F₁` of all restrictions to `E₁` of functions of `F`, and for each such restriction `f₁`,
`‖f₁‖₁` is the minimum of `‖f‖` over all `f ∈ F` whose restriction to `E₁` is `f₁`.
Stated as: an RKHS on `E₁` with the restricted kernel exists, and every RKHS on `E₁` with the
restricted kernel has exactly the restrictions as its functions and the attained minimum as
its norm. -/
theorem restriction_theorem {X : Type u} (H : Type v) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ] (E₁ : Set X) :
    (∃ (H₁ : Type u) (_ : NormedAddCommGroup H₁) (_ : InnerProductSpace ℂ H₁)
        (_ : CompleteSpace H₁) (_ : RKHS ℂ H₁ E₁ ℂ),
        ∀ x y : E₁, kernelFn H₁ x y = kernelFn H (x : X) (y : X)) ∧
    ∀ (H₁ : Type w) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
        [RKHS ℂ H₁ E₁ ℂ], (∀ x y : E₁, kernelFn H₁ x y = kernelFn H (x : X) (y : X)) →
      Set.range (fun f₁ : H₁ => (⇑f₁ : E₁ → ℂ)) =
          {φ : E₁ → ℂ | ∃ f : H, φ = fun x : E₁ => f (x : X)} ∧
      ∀ f₁ : H₁, IsLeast
        {r : ℝ | ∃ f : H, (fun x : E₁ => f (x : X)) = (⇑f₁ : E₁ → ℂ) ∧ r = ‖f‖} ‖f₁‖ := by sorry

end AronszajnRK.Product
