-- Prove2me | Theorems.Thm_AronszajnRK_Inclusion_equivalent_norms_same_class
-- name    : AronszajnRK.Inclusion.equivalent_norms_same_class
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:08:04.7452+00:00
-- url     : https://prove2.me/theorems/be863cc1-070d-4e98-be6d-d0206b603679
-- title:
--   §13 (C), Corollary IV₁ — two RKHS norms on the same class are equivalent
-- statement:
--   Let $\|\cdot\|$ and $\|\cdot\|_1$ be two norms each giving the same (R.K.)-class $F$ of complex functions on $X$ the structure of a Hilbert space with a reproducing kernel. Then there are constants $m>0$ and $M>0$ such that
--
--   $$m\,\|f\| \ \le\ \|f\|_1 \ \le\ M\,\|f\| \qquad\text{for every } f\in F .$$
--
--   In particular, the Hilbert-space topology of an (R.K.)-class does not depend on the choice of admissible norm.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 383, §13 (C), Corollary IV₁

import Mathlib

namespace AronszajnRK.Inclusion

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §13 (C),
Corollary IV₁, p. 383 (PDF p. 47). Let `‖ ‖` and `‖ ‖₁` be two norms corresponding to the same
(R.K.)-class `F`. There exist two positive constants `m` and `M` such that
`m‖f‖ ≤ ‖f‖₁ ≤ M‖f‖` for `f ∈ F`. The two norms are those of RKHSs `H` and `H₁` with the same
class of functions. -/
theorem equivalent_norms_same_class {X H H₁ : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [RKHS ℂ H₁ X ℂ]
    (heq : Set.range (fun f₁ : H₁ => ⇑f₁) = Set.range (fun f : H => ⇑f)) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧
      ∀ (f : H) (f₁ : H₁), ⇑f = ⇑f₁ → m * ‖f‖ ≤ ‖f₁‖ ∧ ‖f₁‖ ≤ M * ‖f‖ := by sorry

end AronszajnRK.Inclusion
