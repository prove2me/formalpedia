-- Prove2me | Theorems.Thm_AronszajnRK_Limits_kernel_diag_antitone
-- name    : AronszajnRK.Limits.kernel_diag_antitone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:11:43.162963+00:00
-- url     : https://prove2.me/theorems/b33037d8-f91c-4f68-b907-c69fc43dc78c
-- title:
--   §9, proof of Theorem I — the diagonal values $K_m(y,y)$, $m\ge k$, decrease and are non-negative
-- statement:
--   Assume the standing assumptions (1)–(3) of §9 A, with reproducing kernels $K_n$ of the classes $F_n$ on $E_n$. Fix $k$ and a point $y\in E_k$, so that $K_m(y,y)$ is defined for every $m\ge k$. Then
--
--   $$K_k(y,y)\ \ge\ K_{k+1}(y,y)\ \ge\ K_{k+2}(y,y)\ \ge\ \cdots\ \ge\ 0,$$
--
--   i.e. $\{K_m(y,y)\}_{m\ge k}$ is a decreasing sequence of non-negative real numbers.
--
--   This is the step that makes the sequence $K_m(y,y)$ convergent in the proof of Theorem I.
--
--   **Formalization Note** The values are complex numbers compared in Mathlib's `ComplexOrder` ($z\le w$ iff $\operatorname{Re} z\le\operatorname{Re} w$ and $\operatorname{Im} z=\operatorname{Im} w$), so the statement also asserts that the values are real. The sequence is indexed as $m=k+j$, $j=0,1,\dots$
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 363, §9, proof of Theorem I

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn
import Definitions.Def_AronszajnRK_Limits_IsDecreasingRKSequence

open scoped ComplexOrder

namespace AronszajnRK.Limits

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §9, proof of
Theorem I, p. 363, PDF p. 27. Under the standing assumptions (1)–(3) of §9 A, for a point
`y ∈ E k` the diagonal values `Kₘ(y, y)`, `m ≥ k`, form a decreasing sequence of non-negative
numbers. The order on `ℂ` is `ComplexOrder` (`z ≤ w` iff `re z ≤ re w` and `im z = im w`), so
the statement also records that these values are real. The sequence is indexed as `m = k + j`. -/
theorem kernel_diag_antitone {X : Type*} (E : ℕ → Set X) (H : ℕ → Type*)
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)] [∀ n, CompleteSpace (H n)]
    [∀ n, RKHS ℂ (H n) (E n) ℂ] (hS : IsDecreasingRKSequence E H) (k : ℕ) (y : X)
    (hy : y ∈ E k) :
    Antitone (fun j : ℕ => AronszajnRK.Sum.kernelFn (H (k + j)) ⟨y, hS.mono (Nat.le_add_right k j) hy⟩
        ⟨y, hS.mono (Nat.le_add_right k j) hy⟩) ∧
      ∀ j : ℕ, 0 ≤ AronszajnRK.Sum.kernelFn (H (k + j)) ⟨y, hS.mono (Nat.le_add_right k j) hy⟩
        ⟨y, hS.mono (Nat.le_add_right k j) hy⟩ := by sorry

end AronszajnRK.Limits
