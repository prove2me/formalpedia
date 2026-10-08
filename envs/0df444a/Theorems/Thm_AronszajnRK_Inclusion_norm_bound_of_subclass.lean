-- Prove2me | Theorems.Thm_AronszajnRK_Inclusion_norm_bound_of_subclass
-- name    : AronszajnRK.Inclusion.norm_bound_of_subclass
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:07:52.558207+00:00
-- url     : https://prove2.me/theorems/40853d2f-0cde-4b1e-a750-e4d74e6fd69f
-- title:
--   §13 (C), Theorem IV — an inclusion of (R.K.)-classes is bounded
-- statement:
--   Let $F$ and $F_1\subset F$ be (R.K.)-classes of complex functions on $X$, and let $\|\cdot\|$, $\|\cdot\|_1$ be any norms giving $F$ and $F_1$ the structure of Hilbert spaces with reproducing kernels. Then there is a constant $M>0$ such that
--
--   $$\|f\| \ \le\ M\,\|f\|_1 \qquad\text{for every } f\in F_1 .$$
--
--   The constant depends on the two norms but not on $f$. This is the automatic-continuity statement behind the inclusion criterion of Corollary IV₂.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 382, §13 (C), Theorem IV

import Mathlib

namespace AronszajnRK.Inclusion

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §13 (C),
Theorem IV, p. 382 (PDF p. 46). Let `F` and `F₁ ⊂ F` be (R.K.)-classes and `‖ ‖`, `‖ ‖₁` some norms
corresponding to `F` and `F₁`. Then there exists a constant `M > 0` such that `‖f‖ ≤ M‖f‖₁` for
`f ∈ F₁`. The norms are those of arbitrary RKHSs `H` and `H₁` with these classes of functions. -/
theorem norm_bound_of_subclass {X H H₁ : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [RKHS ℂ H₁ X ℂ]
    (hsub : Set.range (fun f₁ : H₁ => ⇑f₁) ⊆ Set.range (fun f : H => ⇑f)) :
    ∃ M : ℝ, 0 < M ∧ ∀ (f₁ : H₁) (f : H), ⇑f = ⇑f₁ → ‖f‖ ≤ M * ‖f₁‖ := by sorry

end AronszajnRK.Inclusion
