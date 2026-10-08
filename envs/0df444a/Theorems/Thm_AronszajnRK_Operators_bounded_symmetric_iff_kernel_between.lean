-- Prove2me | Theorems.Thm_AronszajnRK_Operators_bounded_symmetric_iff_kernel_between
-- name    : AronszajnRK.Operators.bounded_symmetric_iff_kernel_between
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:13:04.793367+00:00
-- url     : https://prove2.me/theorems/2a7f3419-eda3-45c6-8f9f-931a18953e0f
-- title:
--   §11, Theorem I — a hermitian $\Lambda$ is the kernel of a symmetric operator with bounds $m, M$ iff $mK \ll \Lambda \ll MK$
-- statement:
--   Let $F$ be a complex Hilbert space of functions on a set $E$ with reproducing kernel $K$. Let $\Lambda : E \times E \to \mathbb{C}$ be an arbitrary hermitian symmetric kernel, $\Lambda(x, y) = \overline{\Lambda(y, x)}$, and let $m, M$ be real numbers. Then $\Lambda$ is the kernel of a bounded symmetric operator $L$ on $F$ with lower bound $\ge m$ and upper bound $\le M$, i.e.
--   $$
--   m\,(f, f) \le (Lf, f) \le M\,(f, f) \qquad \text{for every } f \in F,
--   $$
--   if and only if
--   $$
--   mK \ll \Lambda \ll MK,
--   $$
--   that is, both $\Lambda - mK$ and $MK - \Lambda$ are positive matrices.
--
--   The theorem characterizes, purely in terms of finite quadratic forms of the kernels, which functions of two points are kernels of bounded symmetric operators, and with which bounds. It is not assumed that $\Lambda(\cdot, y)$ belongs to $F$: this is part of what the condition implies.
--
--   **Formalization Note.** The kernel of $L$ is `opKernel L` ($\Lambda(x,y) = L^*_x K(x, y)$), symmetry is `IsSelfAdjoint L`, and the bounds are those of the quadratic form, `m‖f‖² ≤ Re⟪f, L f⟫_ℂ ≤ M‖f‖²` (for symmetric $L$ the number $\langle f, Lf\rangle$ is real); they are not bounds on the operator norm. The order $\ll$ is `KernelLE` (`Matrix.PosSemidef` of the difference). The paper does not assume $m \le M$ and neither does the statement: for $m > M$ each side holds exactly when $F = \{0\}$ and $\Lambda = 0$, so the equivalence still holds.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 373, §11, Theorem I

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn
import Definitions.Def_AronszajnRK_Operators_opKernel
import Definitions.Def_AronszajnRK_Limits_KernelLE

open scoped InnerProductSpace
open ComplexConjugate

namespace AronszajnRK.Operators

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §11,
Theorem I, p. 373 (PDF p. 37). Let `H` be a complex reproducing kernel Hilbert space of
functions on `X` with kernel `K`, and `Λ : X → X → ℂ` an arbitrary hermitian symmetric kernel,
`Λ(x, y) = \overline{Λ(y, x)}`. For real `m, M`, `Λ` is the kernel (§11, Eq. (1)) of a bounded
symmetric operator `L` with lower bound `≥ m` and upper bound `≤ M`, i.e.
`m (f, f) ≤ (Lf, f) ≤ M (f, f)` for every `f`, if and only if `mK ≪ Λ ≪ MK`.
It is not assumed that `Λ(·, y)` belongs to `H`, nor that `m ≤ M`. -/
theorem bounded_symmetric_iff_kernel_between {H : Type*} {X : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ]
    (Λ : X → X → ℂ) (hΛ : ∀ x y : X, Λ x y = conj (Λ y x)) (m M : ℝ) :
    (∃ L : H →L[ℂ] H, IsSelfAdjoint L ∧ opKernel L = Λ ∧
        ∀ f : H, m * ‖f‖ ^ 2 ≤ RCLike.re ⟪f, L f⟫_ℂ ∧ RCLike.re ⟪f, L f⟫_ℂ ≤ M * ‖f‖ ^ 2) ↔
      (AronszajnRK.Limits.KernelLE (fun x y => (m : ℂ) * AronszajnRK.Sum.kernelFn H x y) Λ ∧
        AronszajnRK.Limits.KernelLE Λ (fun x y => (M : ℂ) * AronszajnRK.Sum.kernelFn H x y)) := by sorry

end AronszajnRK.Operators
