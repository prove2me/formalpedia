-- Prove2me | Theorems.Thm_DiazModulus_diaz_of_exp_eq_one
-- name    : DiazModulus.diaz_of_exp_eq_one
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T04:26:25.655996+00:00
-- url     : https://prove2.me/theorems/2d041e86-17d2-42c5-884b-7a697d9800ba
-- title:
--   The case where the exponential is 1
-- statement:
--   **Diaz's conjecture in the case $e^{u} = 1$.**
--
--   If $u \neq 0$ is non-real with $|u|$ algebraic and $e^{u} = 1$, then $e^{u}$ is
--   transcendental.
--
--   **The statement is vacuously satisfiable only if $\pi$ is algebraic, so it is settled.**
--   $e^{u} = 1$ forces $u = 2\pi i n$ for some integer $n$, and $u \neq 0$ forces
--   $n \neq 0$. Then
--   $$|u| = 2\pi|n|,$$
--   so $|u|$ algebraic would make $\pi = |u| / (2|n|)$ algebraic, the algebraic numbers
--   being a field. Transcendence of $\pi$ — available on this mission as
--   `DiazModulus.pi_transcendental` — rules that out. The hypotheses are contradictory and
--   the conclusion follows.
--
--   Note the conclusion is in fact false at such $u$ if one ignores the hypotheses, since
--   $e^{u} = 1$ is algebraic. What is proved is that no $u$ satisfies the hypotheses at
--   all — which is exactly what is needed, and why this case is *closed* rather than
--   *true for interesting reasons*.
--
--   **Position.** One half of a split of `DiazModulus.diaz_of_exp_real_self_not_real` on
--   whether $e^{u} = 1$. That node sits under `DiazModulus.diaz_of_exp_real`, which sits
--   under the modulus conjecture, and both reductions are already accepted — so closing this
--   and its sibling propagates upward.
--
--   Every split on this mission is on the ambient space, so each child is *strictly weaker*
--   than its parent rather than a restatement of it. Weaker is not the same as easier, and
--   no claim of the latter is made.

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem diaz_of_exp_eq_one :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im = 0 →
      u.im ≠ 0 → Complex.exp u = 1 → Transcendental ℚ (Complex.exp u) := by sorry
end DiazModulus
