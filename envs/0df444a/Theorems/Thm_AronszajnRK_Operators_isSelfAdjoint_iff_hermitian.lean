-- Prove2me | Theorems.Thm_AronszajnRK_Operators_isSelfAdjoint_iff_hermitian
-- name    : AronszajnRK.Operators.isSelfAdjoint_iff_hermitian
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:12:28.218986+00:00
-- url     : https://prove2.me/theorems/74f71b43-5063-48de-83fa-95956a1149e0
-- title:
--   §11, (6) — $L$ is symmetric iff its kernel is hermitian symmetric
-- statement:
--   Let $F$ be a complex Hilbert space of functions on a set $E$ with reproducing kernel $K$, and let $L$ be a bounded operator on $F$ with kernel $\Lambda(x, y) = L^*_x K(x, y)$. Then $L$ is symmetric ($L = L^*$) if and only if $\Lambda$ is hermitian symmetric:
--   $$
--   L = L^* \iff \Lambda(x, y) = \overline{\Lambda(y, x)} \quad \text{for all } x, y \in E.
--   $$
--
--   This identifies the symmetric bounded operators with the hermitian kernels, the class of kernels to which the main theorem of the mission applies.
--
--   **Formalization Note.** Symmetry of a bounded operator is `IsSelfAdjoint L`, i.e. `adjoint L = L`.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 372, §11, (6)

import Mathlib
import Definitions.Def_AronszajnRK_Operators_opKernel

open ComplexConjugate

namespace AronszajnRK.Operators

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §11, (6),
p. 372 (PDF p. 36): a bounded operator `L` on a complex reproducing kernel Hilbert space is
symmetric (self-adjoint) if and only if its kernel `Λ` (§11, Eq. (1)) is hermitian symmetric,
`Λ(x, y) = \overline{Λ(y, x)}` for all `x, y`. -/
theorem isSelfAdjoint_iff_hermitian {H : Type*} {X : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ] (L : H →L[ℂ] H) :
    IsSelfAdjoint L ↔ ∀ x y : X, opKernel L x y = conj (opKernel L y x) := by sorry

end AronszajnRK.Operators
