-- Prove2me | Theorems.Thm_AronszajnRK_Inclusion_subclass_of_dominated
-- name    : AronszajnRK.Inclusion.subclass_of_dominated
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:29:16.168812+00:00
-- url     : https://prove2.me/theorems/e352513e-6491-422f-862c-c315724786ca
-- title:
--   §7, Theorem I — $K_1 \ll K$ implies $F_1\subset F$ and $\|f_1\|_1 \ge \|f_1\|$
-- statement:
--   Let $F$ and $F_1$ be classes of complex functions on a set $X$ forming complex Hilbert spaces with reproducing kernels $K$ and $K_1$, with norms $\|\cdot\|$ and $\|\cdot\|_1$. If
--
--   $$K_1 \ll K,$$
--
--   then $F_1\subset F$, and $\|f_1\|_1\ge\|f_1\|$ for every $f_1\in F_1$.
--
--   This is the sufficiency half of the inclusion criterion: domination of kernels gives a contractive inclusion of the classes.
--
--   **Formalization Note** $F$ and $F_1$ are Mathlib `RKHS` instances `H`, `H₁` over $\mathbb C$; "$F_1\subset F$" is inclusion of their sets of functions, and the norm comparison is between the element of $H_1$ and the element of $H$ that are the same function.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 354, §7, Theorem I

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn
import Definitions.Def_AronszajnRK_Limits_KernelLE

namespace AronszajnRK.Inclusion

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §7, Theorem I,
p. 354 (PDF p. 18). If `K` and `K₁` are the reproducing kernels of the classes `F` and `F₁` with
the norms `‖ ‖`, `‖ ‖₁`, and if `K₁ ≪ K`, then `F₁ ⊂ F` and `‖f₁‖₁ ≥ ‖f₁‖` for every `f₁ ∈ F₁`.
The classes are complex RKHSs `H` (norm `‖ ‖`) and `H₁` (norm `‖ ‖₁`) of functions on `X`; the norm
comparison is between the elements of `H₁` and of `H` carrying the same function. -/
theorem subclass_of_dominated {X H H₁ : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [RKHS ℂ H₁ X ℂ]
    (hK : AronszajnRK.Limits.KernelLE (AronszajnRK.Sum.kernelFn H₁) (AronszajnRK.Sum.kernelFn H)) :
    Set.range (fun f₁ : H₁ => ⇑f₁) ⊆ Set.range (fun f : H => ⇑f) ∧
      ∀ (f₁ : H₁) (f : H), ⇑f = ⇑f₁ → ‖f‖ ≤ ‖f₁‖ := by sorry

end AronszajnRK.Inclusion
