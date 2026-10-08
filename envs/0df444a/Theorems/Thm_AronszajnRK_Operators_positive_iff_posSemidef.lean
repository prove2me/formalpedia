-- Prove2me | Theorems.Thm_AronszajnRK_Operators_positive_iff_posSemidef
-- name    : AronszajnRK.Operators.positive_iff_posSemidef
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:12:38.794383+00:00
-- url     : https://prove2.me/theorems/03576c6f-5225-4fb9-b55e-7c0ffeeebb83
-- title:
--   §11, (7) — $L$ is positive iff its kernel is a positive matrix
-- statement:
--   Let $F$ be a complex Hilbert space of functions on a set $E$ with reproducing kernel $K$, and let $L$ be a bounded operator on $F$ with kernel $\Lambda(x, y) = L^*_x K(x, y)$. The operator $L$ is **positive** if $(Lf, f) \ge 0$ for every $f \in F$, that is, the complex number $(Lf, f)$ is real and nonnegative. Then
--   $$
--   L \text{ is positive} \iff \Lambda \text{ is a positive matrix},
--   $$
--   where a positive matrix is a hermitian $P$ with $\sum_{i,j} \overline{\xi_i} P(y_i, y_j) \xi_j \ge 0$ for all finite families of points $y_i$ and complex numbers $\xi_i$.
--
--   Positivity of an operator is thus read off its kernel. Applied to $L - mI$ and $MI - L$, whose kernels are $\Lambda - mK$ and $MK - \Lambda$, this gives the necessity half of the mission's main theorem.
--
--   **Formalization Note.** Positivity is written `∀ f, 0 ≤ ⟪f, L f⟫_ℂ` with the `ComplexOrder` on `ℂ` (real part nonnegative and imaginary part zero). It does not assume that $L$ is self-adjoint; over $\mathbb{C}$ it is equivalent to Mathlib's `ContinuousLinearMap.IsPositive` (`isPositive_iff_complex`), in agreement with the paper's remark that a positive operator is always symmetric. The kernel matrix is `Matrix.of (opKernel L)` and positivity of a matrix is `Matrix.PosSemidef`.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 372, §11, (7)

import Mathlib
import Definitions.Def_AronszajnRK_Operators_opKernel

open scoped InnerProductSpace ComplexOrder

namespace AronszajnRK.Operators

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §11, (7),
p. 372 (PDF p. 36): a bounded operator `L` on a complex reproducing kernel Hilbert space is
positive, i.e. `(Lf, f) ≥ 0` for every `f` (the scalar `(Lf, f) = ⟪f, L f⟫_ℂ` is real and
nonnegative; `≤` on `ℂ` is `ComplexOrder`), if and only if its kernel `Λ` (§11, Eq. (1)) is a
positive matrix. No self-adjointness of `L` is assumed. -/
theorem positive_iff_posSemidef {H : Type*} {X : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ] (L : H →L[ℂ] H) :
    (∀ f : H, 0 ≤ ⟪f, L f⟫_ℂ) ↔ (Matrix.of (opKernel L : X → X → ℂ)).PosSemidef := by sorry

end AronszajnRK.Operators
