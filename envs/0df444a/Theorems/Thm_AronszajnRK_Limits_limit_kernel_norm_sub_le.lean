-- Prove2me | Theorems.Thm_AronszajnRK_Limits_limit_kernel_norm_sub_le
-- name    : AronszajnRK.Limits.limit_kernel_norm_sub_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:11:56.217389+00:00
-- url     : https://prove2.me/theorems/5aca64cf-e14d-46d7-89a6-850a76f085b7
-- title:
--   §9, proof of Theorem I, Eq. (6) — $\|K_{mk}(\cdot,y)-K_{0k}(\cdot,y)\|_k^2 \le K_m(y,y)-K_0(y,y)$
-- statement:
--   Assume the standing assumptions (1)–(3) of §9 A, with reproducing kernels $K_n$ of the classes $F_n$ on $E_n$. Let $K_0 : E\times E\to\mathbb C$ be the limit of the kernels in the sense of §9: whenever $x,y\in E_N$, $K_n(x,y)\to K_0(x,y)$ as $n\to\infty$ ($K_n(x,y)$ being defined for $n\ge N$). Fix $y\in E_k$ and $m\ge k$. Then
--
--   1. the restriction $K_{0k}(\cdot,y)$ of $K_0(\cdot,y)$ to $E_k$ belongs to $F_k$; and
--   2. for the restriction $K_{mk}(\cdot,y)\in F_k$ of $K_m(\cdot,y)$,
--   $$\|K_{mk}(\cdot,y)-K_{0k}(\cdot,y)\|_k^2\ \le\ K_m(y,y)-K_0(y,y).$$
--
--   This estimate drives both the membership of $K_0(\cdot,y)$ in $F_0$ and the reproducing property of $K_0$.
--
--   **Formalization Note** $K_0$ is a variable pinned by the convergence hypothesis; since every pair $x,y$ lies in some $E_N$, that hypothesis determines $K_0$ uniquely, and Theorem I (the goal) shows it is satisfiable. The inequality is in `ComplexOrder`, so it also asserts that the right-hand side is real. The sequence index $n\ge N$ is written $N+j$.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 363, §9, proof of Theorem I, Eq. (6)

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn
import Definitions.Def_AronszajnRK_Limits_IsDecreasingRKSequence

open Filter Topology
open scoped ComplexOrder

namespace AronszajnRK.Limits

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §9, proof of
Theorem I, p. 363, PDF p. 27, the sentence before Eq. (6) and Eq. (6) (first line). Under the
standing assumptions (1)–(3) of §9 A, let `K₀` be the limit of the kernels in the sense of p. 363:
for `x, y ∈ E N`, `K_{N+j}(x, y) → K₀(x, y)` as `j → ∞`. Fix `y ∈ E k` and `m ≥ k`. Then the
restriction `K₀ₖ(·, y)` of `K₀(·, y)` to `E k` belongs to `H k`, and for the restriction
`a = Kₘₖ(·, y) ∈ H k` of `Kₘ(·, y)` one has `‖Kₘₖ(·, y) − K₀ₖ(·, y)‖ₖ² ≤ Kₘ(y, y) − K₀(y, y)`
(in `ComplexOrder`). -/
theorem limit_kernel_norm_sub_le {X : Type*} (E : ℕ → Set X) (H : ℕ → Type*)
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)] [∀ n, CompleteSpace (H n)]
    [∀ n, RKHS ℂ (H n) (E n) ℂ] (hS : IsDecreasingRKSequence E H) (K₀ : X → X → ℂ)
    (hK₀ : ∀ (x y : X) (N : ℕ) (hx : x ∈ E N) (hy : y ∈ E N),
      Tendsto (fun j : ℕ => AronszajnRK.Sum.kernelFn (H (N + j)) ⟨x, hS.mono (Nat.le_add_right N j) hx⟩
        ⟨y, hS.mono (Nat.le_add_right N j) hy⟩) atTop (𝓝 (K₀ x y)))
    {k m : ℕ} (hkm : k ≤ m) (y : X) (hy : y ∈ E k) :
    (∃ c : H k, ∀ x : E k, c x = K₀ x.1 y) ∧
      ∀ a c : H k,
        (∀ x : E k, a x = AronszajnRK.Sum.kernelFn (H m) (Set.inclusion (hS.mono hkm) x) ⟨y, hS.mono hkm hy⟩) →
        (∀ x : E k, c x = K₀ x.1 y) →
        ((‖a - c‖ ^ 2 : ℝ) : ℂ) ≤ AronszajnRK.Sum.kernelFn (H m) ⟨y, hS.mono hkm hy⟩ ⟨y, hS.mono hkm hy⟩ - K₀ y y := by sorry

end AronszajnRK.Limits
