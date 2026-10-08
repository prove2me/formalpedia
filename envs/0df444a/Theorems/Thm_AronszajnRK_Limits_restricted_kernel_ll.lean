-- Prove2me | Theorems.Thm_AronszajnRK_Limits_restricted_kernel_ll
-- name    : AronszajnRK.Limits.restricted_kernel_ll
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:11:43.398803+00:00
-- url     : https://prove2.me/theorems/fbdff6de-0d8b-4380-ade6-ca1671c75d9e
-- title:
--   §9, Eq. (4) — the restricted kernels satisfy $K_{nm} \ll K_m$ for $m<n$
-- statement:
--   Assume the standing assumptions (1)–(3) of §9 A: sets $E_1\subset E_2\subset\cdots$ with union $X$, complex Hilbert spaces $F_n$ of functions on $E_n$ with reproducing kernels $K_n$, the restriction to $E_m$ of an element of $F_n$ lies in $F_m$ and has no larger norm ($m\le n$). For $m\le n$ let $K_{nm}$ be the restriction of $K_n$ to $E_m\times E_m$. Then for $m<n$
--
--   $$K_{nm} \ll K_m ,$$
--
--   that is, $K_m - K_{nm}$ is a positive matrix on $E_m$.
--
--   This comparison of kernels on a common set is what makes the diagonal values $K_n(y,y)$ decrease, and hence the kernels converge.
--
--   **Formalization Note** $\ll$ is `KernelLE`, defined through Mathlib's `Matrix.PosSemidef`. The restriction $K_{nm}$ is $K_n$ evaluated at the images of points of $E_m$ under the inclusion $E_m\subset E_n$.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 362, §9, Eq. (4)

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn
import Definitions.Def_AronszajnRK_Limits_IsDecreasingRKSequence
import Definitions.Def_AronszajnRK_Limits_KernelLE

namespace AronszajnRK.Limits

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §9, Eq. (4),
p. 362, PDF p. 26. Under the standing assumptions (1)–(3) of §9 A, for `m < n` the restriction
`Kₙₘ` of `Kₙ` to `Eₘ × Eₘ` satisfies `Kₙₘ ≪ Kₘ`, i.e. `Kₘ − Kₙₘ` is a positive matrix on `Eₘ`. -/
theorem restricted_kernel_ll {X : Type*} (E : ℕ → Set X) (H : ℕ → Type*)
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)] [∀ n, CompleteSpace (H n)]
    [∀ n, RKHS ℂ (H n) (E n) ℂ] (hS : IsDecreasingRKSequence E H) {m n : ℕ} (hmn : m < n) :
    KernelLE
      (fun x y : E m => AronszajnRK.Sum.kernelFn (H n) (Set.inclusion (hS.mono hmn.le) x)
        (Set.inclusion (hS.mono hmn.le) y))
      (AronszajnRK.Sum.kernelFn (H m)) := by sorry

end AronszajnRK.Limits
