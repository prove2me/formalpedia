-- Prove2me | Theorems.Thm_AronszajnRK_Inclusion_eq_class_iff_kernel_two_sided
-- name    : AronszajnRK.Inclusion.eq_class_iff_kernel_two_sided
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:29:35.892238+00:00
-- url     : https://prove2.me/theorems/22cced17-17e3-442e-a492-a98046617898
-- title:
--   §13 (C), Corollary IV₃ — $F_1 = F$ iff $mK \ll K_1 \ll MK$
-- statement:
--   Let $K$ and $K_1$ be positive matrices on a set $X$ and $F$, $F_1$ the corresponding classes of complex functions. Then
--
--   $$F_1 = F \iff \text{there are constants } m>0,\ M>0 \text{ with } mK \ll K_1 \ll MK .$$
--
--   Two kernels thus define the same function class exactly when each is dominated by a multiple of the other.
--
--   **Formalization Note** As for Corollary IV₂: stated for arbitrary complex `RKHS` instances $H$, $H_1$ with scalar kernels $K$, $K_1$; "$F_1 = F$" is equality of their sets of functions.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 383, §13 (C), Corollary IV₃

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn
import Definitions.Def_AronszajnRK_Limits_KernelLE

namespace AronszajnRK.Inclusion

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §13 (C),
Corollary IV₃, p. 383 (PDF p. 47). Under the hypotheses of Corollary IV₂ (`K`, `K₁` positive
matrices, `F`, `F₁` the corresponding classes), in order that `F₁ = F` it is necessary and
sufficient that there exist two positive constants `m` and `M` such that `mK ≪ K₁ ≪ MK`.
Stated, as Corollary IV₂, for arbitrary complex RKHSs `H`, `H₁` with kernels `K`, `K₁`. -/
theorem eq_class_iff_kernel_two_sided {X H H₁ : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [RKHS ℂ H₁ X ℂ] :
    Set.range (fun f₁ : H₁ => ⇑f₁) = Set.range (fun f : H => ⇑f) ↔
      ∃ m M : ℝ, 0 < m ∧ 0 < M ∧
        AronszajnRK.Limits.KernelLE (fun x y => (m : ℂ) * AronszajnRK.Sum.kernelFn H x y) (AronszajnRK.Sum.kernelFn H₁) ∧
        AronszajnRK.Limits.KernelLE (AronszajnRK.Sum.kernelFn H₁) (fun x y => (M : ℂ) * AronszajnRK.Sum.kernelFn H x y) := by sorry

end AronszajnRK.Inclusion
