-- Prove2me | Theorems.Thm_AronszajnRK_Operators_kernel_limits
-- name    : AronszajnRK.Operators.kernel_limits
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:12:51.530382+00:00
-- url     : https://prove2.me/theorems/869438ba-dd1d-4a8a-aa5b-1724a46a877d
-- title:
--   §11, Theorem II — weak and uniform limits of operators give pointwise and uniform limits of kernels
-- statement:
--   Let $F$ be a complex Hilbert space of functions on a set $E$ with reproducing kernel $K$, let $L, L_1, L_2, \dots$ be bounded operators on $F$, and let $\Lambda, \Lambda_1, \Lambda_2, \dots$ be their kernels.
--
--   1. If $L = \text{w.}\lim L_n$, i.e. $L_n u$ converges weakly to $Lu$ for every $u \in F$, then
--   $$
--   \Lambda(x, y) = \lim_{n \to \infty} \Lambda_n(x, y) \qquad \text{for every } x, y \in E.
--   $$
--   2. If $L = \text{un.}\lim L_n$, i.e. $\|L_n - L\| \to 0$ in operator norm, then $\Lambda_n$ converges to $\Lambda$ uniformly on every set $S$ of couples $(x, y)$ on which $K(x, x)$ and $K(y, y)$ are uniformly bounded.
--
--   Convergence of operators thus transfers to convergence of their kernels, pointwise under weak convergence and locally uniformly under norm convergence.
--
--   **Formalization Note.** Weak convergence of $L_n u$ to $L u$ is written $\langle v, L_n u\rangle \to \langle v, L u\rangle$ for every $v$. The uniform bound on the set $S \subseteq E \times E$ is $|K(x,x)| \le C$ and $|K(y,y)| \le C$ for all $(x,y) \in S$, with one constant $C$.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 374, §11, Theorem II

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn
import Definitions.Def_AronszajnRK_Operators_opKernel

open scoped InnerProductSpace Topology
open Filter

namespace AronszajnRK.Operators

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §11,
Theorem II, p. 374 (PDF p. 38). Let `Lₙ`, `L` be bounded operators on a complex reproducing
kernel Hilbert space with kernel `K`, and `Λₙ`, `Λ` their kernels (§11, Eq. (1)).
1. If `L = w. lim Lₙ` (`Lₙ u` converges weakly to `L u` for every `u`, i.e. `⟪v, Lₙ u⟫ → ⟪v, L u⟫`
   for all `u, v`), then `Λₙ(x, y) → Λ(x, y)` for every `x, y`.
2. If `L = un. lim Lₙ` (`‖Lₙ − L‖ → 0`, operator norm), then `Λₙ → Λ` uniformly on every set
   of couples `(x, y)` on which `K(x, x)` and `K(y, y)` are uniformly bounded. -/
theorem kernel_limits {H : Type*} {X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [RKHS ℂ H X ℂ] (L : H →L[ℂ] H) (Ls : ℕ → H →L[ℂ] H) :
    ((∀ u v : H, Tendsto (fun n => ⟪v, Ls n u⟫_ℂ) atTop (𝓝 ⟪v, L u⟫_ℂ)) →
        ∀ x y : X, Tendsto (fun n => opKernel (Ls n) x y) atTop (𝓝 (opKernel L x y))) ∧
      (Tendsto (fun n => ‖Ls n - L‖) atTop (𝓝 0) →
        ∀ S : Set (X × X),
          (∃ C : ℝ, ∀ p ∈ S, ‖AronszajnRK.Sum.kernelFn H p.1 p.1‖ ≤ C ∧ ‖AronszajnRK.Sum.kernelFn H p.2 p.2‖ ≤ C) →
            TendstoUniformlyOn (fun n (p : X × X) => opKernel (Ls n) p.1 p.2)
              (fun p => opKernel L p.1 p.2) atTop S) := by sorry

end AronszajnRK.Operators
