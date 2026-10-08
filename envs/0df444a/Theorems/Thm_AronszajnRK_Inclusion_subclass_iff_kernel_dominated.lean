-- Prove2me | Theorems.Thm_AronszajnRK_Inclusion_subclass_iff_kernel_dominated
-- name    : AronszajnRK.Inclusion.subclass_iff_kernel_dominated
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:29:24.053265+00:00
-- url     : https://prove2.me/theorems/d7c11ed9-273d-41a3-a3aa-1585f93bdc9e
-- title:
--   §13 (C), Corollary IV₂ — $F_1\subset F$ iff $K_1 \ll MK$ for some $M>0$
-- statement:
--   Let $K$ and $K_1$ be positive matrices on a set $X$, and let $F$ and $F_1$ be the corresponding classes of complex functions (the Hilbert spaces with reproducing kernels $K$ and $K_1$). Then
--
--   $$F_1\subset F \iff \text{there is a constant } M>0 \text{ with } K_1 \ll MK .$$
--
--   This turns the inclusion of two function spaces into an inequality between their kernels, which can be checked on finite point sets.
--
--   **Formalization Note** By Moore's theorem (§2 (4)) each positive matrix corresponds to exactly one class, so the statement is given for arbitrary complex `RKHS` instances $H$, $H_1$ with $K$, $K_1$ their scalar kernels; "$F_1\subset F$" is inclusion of their sets of functions. $M$ is a positive real number multiplying the complex kernel $K$.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 383, §13 (C), Corollary IV₂

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn
import Definitions.Def_AronszajnRK_Limits_KernelLE

namespace AronszajnRK.Inclusion

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §13 (C),
Corollary IV₂, p. 383 (PDF p. 47). Let `K` and `K₁` be two positive matrices, `F` and `F₁` the
corresponding classes. In order that `F₁ ⊂ F` it is necessary and sufficient that there exists a
positive constant `M` such that `K₁ ≪ MK`.

By Moore's theorem (§2 (4), p. 344) the class corresponding to a positive matrix is the unique RKHS
with that kernel, so the statement is given for arbitrary complex RKHSs `H`, `H₁` on `X` with
`K := AronszajnRK.Sum.kernelFn H`, `K₁ := AronszajnRK.Sum.kernelFn H₁`. -/
theorem subclass_iff_kernel_dominated {X H H₁ : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [RKHS ℂ H₁ X ℂ] :
    Set.range (fun f₁ : H₁ => ⇑f₁) ⊆ Set.range (fun f : H => ⇑f) ↔
      ∃ M : ℝ, 0 < M ∧ AronszajnRK.Limits.KernelLE (AronszajnRK.Sum.kernelFn H₁) (fun x y => (M : ℂ) * AronszajnRK.Sum.kernelFn H x y) := by sorry

end AronszajnRK.Inclusion
