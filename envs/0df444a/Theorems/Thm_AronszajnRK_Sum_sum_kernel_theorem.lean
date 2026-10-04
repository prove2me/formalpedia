-- Prove2me | Theorems.Thm_AronszajnRK_Sum_sum_kernel_theorem
-- name    : AronszajnRK.Sum.sum_kernel_theorem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T04:49:14.049974+00:00
-- url     : https://prove2.me/theorems/2e9db83c-759a-453e-a5b2-f1da7e53ef74
-- title:
--   §6, Theorem — K₁ + K₂ is the reproducing kernel of F₁ + F₂ with the minimal-decomposition norm
-- statement:
--   Let $E$ be a set and, for $i=1,2$, let $F_i$ be a complex Hilbert space of functions on $E$ with norm $\|\cdot\|_i$ and reproducing kernel $K_i(x,y)$. Then $K(x,y)=K_1(x,y)+K_2(x,y)$ is the reproducing kernel of the class
--   $$F=\{\,f=f_1+f_2 : f_1\in F_1,\ f_2\in F_2\,\}$$
--   with the norm
--   $$\|f\|^2=\min\big[\|f_1\|_1^2+\|f_2\|_2^2\big],$$
--   the minimum taken over all decompositions $f=f_1+f_2$ with $f_i\in F_i$. Precisely:
--
--   1. there is a complex Hilbert space of functions on $E$ with reproducing kernel $K_1+K_2$;
--   2. every complex Hilbert space $F$ of functions on $E$ with reproducing kernel $K_1+K_2$ consists exactly of the functions $f_1+f_2$, and for each $f\in F$ the minimum above is attained and equals $\|f\|^2$.
--
--   The sum theorem is the basic operation of the paper's calculus of kernels: it yields the order relation between kernels and the inclusion theorem of §7, and the kernel of the class of all $f+\bar g$ (§6, p. 354).
--
--   **Formalization Note** The spaces are Mathlib `RKHS ℂ H X ℂ` instances; a decomposition is of functions, $f=f_1+f_2$ pointwise with $f_1\in F_1$, $f_2\in F_2$ (the spaces $F_1$, $F_2$ may share functions). "min" is an attained minimum (`IsLeast`), not an infimum. Part 2 quantifies over every such space in any universe; by Moore's uniqueness (§2 (4)) this describes "the" class with kernel $K_1+K_2$.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 353, §6, Theorem

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn

namespace AronszajnRK.Sum

universe u w

/-- **Sum of reproducing kernels** (Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math.
Soc. 68 (1950), §6, Theorem, p. 353 (PDF 17)): if `Kᵢ(x, y)` is the reproducing kernel of the
class `Fᵢ` with the norm `‖ ‖ᵢ`, then `K(x, y) = K₁(x, y) + K₂(x, y)` is the reproducing kernel of
the class `F` of all functions `f = f₁ + f₂` with `fᵢ ∈ Fᵢ`, and with the norm defined by
`‖f‖² = min [‖f₁‖₁² + ‖f₂‖₂²]`, the minimum taken for all the decompositions `f = f₁ + f₂` with
`fᵢ ∈ Fᵢ`.

Shape: (1) some complex RKHS on `X` has scalar kernel `K₁ + K₂`; (2) every complex RKHS `H` with
scalar kernel `K₁ + K₂` (unique by §2 (4)) consists exactly of the functions `f₁ + f₂`, and for
each `f ∈ H`, `‖f‖²` is the least value (attained minimum) of `‖f₁‖² + ‖f₂‖²` over all
decompositions of the function `f`. -/
theorem sum_kernel_theorem {X : Type u}
    {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [RKHS ℂ H₁ X ℂ]
    {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    [RKHS ℂ H₂ X ℂ] :
    (∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
        (_ : RKHS ℂ H X ℂ), kernelFn H = kernelFn H₁ + kernelFn H₂) ∧
    ∀ (H : Type w) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      [RKHS ℂ H X ℂ], kernelFn H = kernelFn H₁ + kernelFn H₂ →
        Set.range (fun f : H => (f : X → ℂ)) =
            {g : X → ℂ | ∃ (f₁ : H₁) (f₂ : H₂), g = (f₁ : X → ℂ) + (f₂ : X → ℂ)} ∧
        ∀ f : H, IsLeast
          {r : ℝ | ∃ (f₁ : H₁) (f₂ : H₂),
            (f : X → ℂ) = (f₁ : X → ℂ) + (f₂ : X → ℂ) ∧ r = ‖f₁‖ ^ 2 + ‖f₂‖ ^ 2}
          (‖f‖ ^ 2) := by sorry

end AronszajnRK.Sum
