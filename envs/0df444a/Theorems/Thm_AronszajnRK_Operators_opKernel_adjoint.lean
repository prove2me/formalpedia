-- Prove2me | Theorems.Thm_AronszajnRK_Operators_opKernel_adjoint
-- name    : AronszajnRK.Operators.opKernel_adjoint
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:12:24.44899+00:00
-- url     : https://prove2.me/theorems/12e3fea3-be1c-4f93-89f4-720a8626adcd
-- title:
--   §11, (3) — the kernel of the adjoint operator is $\overline{\Lambda(z,y)}$
-- statement:
--   Let $F$ be a complex Hilbert space of functions on a set $E$ with reproducing kernel $K$, let $L$ be a bounded operator on $F$ with kernel $\Lambda(x, y) = L^*_x K(x, y)$, and let $\Lambda^*$ be the kernel of the adjoint operator $L^*$. Then for all $y, z \in E$,
--   $$
--   \Lambda^*(y, z) = \overline{\Lambda(z, y)}.
--   $$
--
--   The kernel of the adjoint is the conjugate transpose of the kernel. This is the identity behind the characterization of symmetric operators by hermitian kernels and the composition formula.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 372, §11, Eq. (3)

import Mathlib
import Definitions.Def_AronszajnRK_Operators_opKernel

open ComplexConjugate

namespace AronszajnRK.Operators

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §11, Eq. (3),
p. 372 (PDF p. 36): the kernel `Λ*` of the adjoint operator `L*` is
`Λ*(y, z) = \overline{Λ(z, y)}`, where `Λ` is the kernel of `L` (§11, Eq. (1)). -/
theorem opKernel_adjoint {H : Type*} {X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [RKHS ℂ H X ℂ] (L : H →L[ℂ] H) (y z : X) :
    opKernel (ContinuousLinearMap.adjoint L) y z = conj (opKernel L z y) := by sorry

end AronszajnRK.Operators
