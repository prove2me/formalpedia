-- Prove2me | Theorems.Thm_AronszajnRK_Limits_restricted_kernel_norm_sub_le
-- name    : AronszajnRK.Limits.restricted_kernel_norm_sub_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:11:51.249985+00:00
-- url     : https://prove2.me/theorems/df15cfc7-4300-4dbf-86ac-61ad0414b6d3
-- title:
--   §9, proof of Theorem I, Eq. (5) — $\|K_{mk}(\cdot,y)-K_{nk}(\cdot,y)\|_k^2 \le K_m(y,y)-K_n(y,y)$
-- statement:
--   Assume the standing assumptions (1)–(3) of §9 A, with reproducing kernels $K_n$ of the classes $F_n$ on $E_n$. Fix $y\in E_k$ and $k\le m\le n$. By (2), the restriction $K_{mk}(\cdot,y)$ of the function $K_m(\cdot,y)\in F_m$ to $E_k$ belongs to $F_k$, and so does the restriction $K_{nk}(\cdot,y)$ of $K_n(\cdot,y)\in F_n$. Then
--
--   $$\|K_{mk}(\cdot,y)-K_{nk}(\cdot,y)\|_k^2\ \le\ K_m(y,y)-K_n(y,y).$$
--
--   Combined with the decrease of $K_m(y,y)$, this shows that $K_{mk}(\cdot,y)$ is a Cauchy sequence in $F_k$ as $m\to\infty$.
--
--   **Formalization Note** The two restrictions are given as elements $a,b$ of $F_k$ whose functions agree with $K_m(\cdot,y)$, resp. $K_n(\cdot,y)$, on $E_k$; such elements exist by (2) and are unique. The inequality is in `ComplexOrder`, so it also asserts that the right-hand side is real.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 363, §9, proof of Theorem I, Eq. (5)

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn
import Definitions.Def_AronszajnRK_Limits_IsDecreasingRKSequence

open scoped ComplexOrder

namespace AronszajnRK.Limits

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §9, proof of
Theorem I, Eq. (5), p. 363, PDF p. 27 (outer inequality). Under the standing assumptions (1)–(3)
of §9 A, fix `y ∈ E k` and `k ≤ m ≤ n`. Let `a ∈ H k` be the restriction `Kₘₖ(·, y)` of
`Kₘ(·, y)` to `E k` and `b ∈ H k` the restriction `Kₙₖ(·, y)` of `Kₙ(·, y)`. Then
`‖a − b‖ₖ² ≤ Kₘ(y, y) − Kₙ(y, y)`. The inequality is in `ComplexOrder`, so it also asserts
that the right-hand side is real. -/
theorem restricted_kernel_norm_sub_le {X : Type*} (E : ℕ → Set X) (H : ℕ → Type*)
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)] [∀ n, CompleteSpace (H n)]
    [∀ n, RKHS ℂ (H n) (E n) ℂ] (hS : IsDecreasingRKSequence E H) {k m n : ℕ} (hkm : k ≤ m)
    (hmn : m ≤ n) (y : X) (hy : y ∈ E k) (a b : H k)
    (ha : ∀ x : E k, a x = AronszajnRK.Sum.kernelFn (H m) (Set.inclusion (hS.mono hkm) x) ⟨y, hS.mono hkm hy⟩)
    (hb : ∀ x : E k, b x = AronszajnRK.Sum.kernelFn (H n) (Set.inclusion (hS.mono (hkm.trans hmn)) x)
      ⟨y, hS.mono (hkm.trans hmn) hy⟩) :
    ((‖a - b‖ ^ 2 : ℝ) : ℂ) ≤ AronszajnRK.Sum.kernelFn (H m) ⟨y, hS.mono hkm hy⟩ ⟨y, hS.mono hkm hy⟩ -
      AronszajnRK.Sum.kernelFn (H n) ⟨y, hS.mono (hkm.trans hmn) hy⟩ ⟨y, hS.mono (hkm.trans hmn) hy⟩ := by sorry

end AronszajnRK.Limits
