-- Prove2me | Theorems.Thm_AronszajnRK_Inclusion_kernel_rescale_norm
-- name    : AronszajnRK.Inclusion.kernel_rescale_norm
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:08:01.604519+00:00
-- url     : https://prove2.me/theorems/44b54247-67dd-4089-9a7d-b2f3096c6028
-- title:
--   §13 (C), p. 382 — the norm $c\|\cdot\|$ has kernel $K/c^2$
-- statement:
--   Let the norm $\|\cdot\|$ give a class $F$ of complex functions on $X$ the structure of a Hilbert space with reproducing kernel $K$, and let $c>0$. Then the norm $\|\cdot\|_1 = c\|\cdot\|$ also gives $F$ the structure of a Hilbert space with a reproducing kernel, and that kernel is
--
--   $$K_1(x,y) = \frac{1}{c^2}\,K(x,y).$$
--
--   The rescaling identity converts a norm comparison $\|f\|\le M\|f\|_1$ into a kernel comparison with the constant $M^2$; it is the link between Theorem IV and Corollaries IV₂, IV₃ of §13.
--
--   **Formalization Note** Two conjuncts: there exists an RKHS with the same functions as $H$ and norm $c\|\cdot\|$; and every RKHS with the same functions as $H$ and norm $c\|\cdot\|$ has scalar kernel $c^{-2}K$.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 382, §13 (C) (unnumbered)

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn

universe uX uH uH₁

namespace AronszajnRK.Inclusion

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §13 (C), p. 382
(PDF p. 46), unnumbered. If the norm `‖ ‖` corresponds to an (R.K.)-class `F`, the norm
`‖ ‖₁ = c‖ ‖`, `c > 0`, also corresponds to `F`, and the corresponding reproducing kernels satisfy
`K₁(x, y) = (1/c²) K(x, y)`.

First conjunct: there is an RKHS `H₁` with the same functions as `H` and norm `c‖ ‖`. Second
conjunct: every RKHS `H₁` with the same functions as `H` and norm `c‖ ‖` has kernel `(1/c²) K`. -/
theorem kernel_rescale_norm {X : Type uX} (H : Type uH)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ]
    (c : ℝ) (hc : 0 < c) :
    (∃ (H₁ : Type uH) (_ : NormedAddCommGroup H₁) (_ : InnerProductSpace ℂ H₁)
        (_ : CompleteSpace H₁) (_ : RKHS ℂ H₁ X ℂ),
        Set.range (fun f₁ : H₁ => ⇑f₁) = Set.range (fun f : H => ⇑f) ∧
          ∀ (f₁ : H₁) (f : H), ⇑f = ⇑f₁ → ‖f₁‖ = c * ‖f‖) ∧
      ∀ (H₁ : Type uH₁) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
        [RKHS ℂ H₁ X ℂ],
        Set.range (fun f₁ : H₁ => ⇑f₁) = Set.range (fun f : H => ⇑f) →
        (∀ (f₁ : H₁) (f : H), ⇑f = ⇑f₁ → ‖f₁‖ = c * ‖f‖) →
        AronszajnRK.Sum.kernelFn H₁ = fun x y => (1 / (c : ℂ) ^ 2) * AronszajnRK.Sum.kernelFn H x y := by sorry

end AronszajnRK.Inclusion
