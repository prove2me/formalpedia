-- Prove2me | Theorems.Thm_AronszajnRK_Limits_restriction_norm_monotone
-- name    : AronszajnRK.Limits.restriction_norm_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:12:08.010019+00:00
-- url     : https://prove2.me/theorems/c5f42a35-bd22-498c-8668-2914d508599e
-- title:
--   §9, Remark after Theorem I — $\|f_{0n}\|_n$ is non-decreasing, so its limit exists in $[0,\infty]$
-- statement:
--   Assume the standing assumptions (1)–(3) of §9 A. Let $f_0$ be a function on $E$ satisfying condition 1° of Theorem I: for every $n$ its restriction $f_{0n}$ to $E_n$ belongs to $F_n$. Then
--
--   $$\|f_{00}\|_0\le\|f_{01}\|_1\le\|f_{02}\|_2\le\cdots,$$
--
--   so $\lim_{n\to\infty}\|f_{0n}\|_n$ exists in the extended reals; it may be infinite.
--
--   The Remark explains why condition 2° of Theorem I is only a finiteness condition.
--
--   **Formalization Note** The limit is asserted in `EReal`. The sequence is indexed from $0$.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 363, §9, Remark after Theorem I

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn
import Definitions.Def_AronszajnRK_Limits_IsDecreasingRKSequence

open Filter Topology

namespace AronszajnRK.Limits

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §9, Remark after
Theorem I, p. 363, PDF p. 27. Under the standing assumptions (1)–(3) of §9 A, let `f₀` be a
function on `E = X` satisfying condition 1° of Theorem I: for every `n`, `g n ∈ H n` is the
restriction `f₀ₙ` of `f₀` to `E n`. Then `n ↦ ‖f₀ₙ‖ₙ` is non-decreasing, so its limit exists in
the extended reals (it may be `+∞`). -/
theorem restriction_norm_monotone {X : Type*} (E : ℕ → Set X) (H : ℕ → Type*)
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)]
    [∀ n, RKHS ℂ (H n) (E n) ℂ] (hS : IsDecreasingRKSequence E H) (f₀ : X → ℂ)
    (g : ∀ n, H n) (hg : ∀ (n : ℕ) (x : E n), g n x = f₀ x.1) :
    Monotone (fun n => ‖g n‖) ∧
      ∃ L : EReal, Tendsto (fun n => ((‖g n‖ : ℝ) : EReal)) atTop (𝓝 L) := by sorry

end AronszajnRK.Limits
