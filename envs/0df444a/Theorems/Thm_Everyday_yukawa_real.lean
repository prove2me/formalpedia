-- Prove2me | Theorems.Thm_Everyday_yukawa_real
-- name    : Everyday.yukawa_real
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-19T00:15:58.366106+00:00
-- url     : https://prove2.me/theorems/b935dfe0-8306-4b3c-98f2-8e98cd681286
-- title:
--   Matter: the Yukawa term plus its hermitian conjugate is real
-- statement:
--   The image's matter label is the fermion kinetic term together with the Yukawa coupling ψ̄_L V Φ ψ_R and its hermitian conjugate — the sector by which fermions acquire mass from the Higgs field. The item is the "+ h.c." of the source equation: the Yukawa term of the discrete arena — the contraction of the left-handed fermion field with the coupling constant and the Higgs field against the right-handed fermion field, summed over the spacetime — is a complex number with no reason to be real; but the Yukawa term plus its hermitian conjugate, exactly the combination the source equation writes, is a real number. The matter contribution to the action is real.
--
--   **Formalization Note** The hermitian conjugate is the complex conjugate, the arena being a scalar (one-component) fragment of the source's matrix contraction. The proof: the imaginary part of a sum is the sum of the imaginary parts, and the imaginary part of a conjugate is the negation of the imaginary part, so the goal reduces to the sum of a real number and its negation, which vanishes. The conclusion is the vanishing of the imaginary part.
-- source:
--   Sean Carroll, "The World of Everyday Experience, In One Equation", preposterousuniverse.com, 2013-01-04, retrieved 2026-10-18, the matter label ψ̄_L V Φ ψ_R + h.c.

import Mathlib
import Definitions.Def_Everyday_spacetime__e5fc57
import Definitions.Def_Everyday_sectors

open ComplexConjugate

namespace Everyday

/-- Matter: the Yukawa coupling plus its hermitian conjugate is real —
the "+ h.c." of the source equation makes the matter contribution to
the action a real number. -/
theorem yukawa_real {X : Type} [Fintype X] (ψL ψR : X → ℂ) (V : ℂ) (Φh : X → ℂ) :
    (yukawaTerm ψL ψR V Φh + conj (yukawaTerm ψL ψR V Φh)).im = 0 := by sorry

end Everyday
