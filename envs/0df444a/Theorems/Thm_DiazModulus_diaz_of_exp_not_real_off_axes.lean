-- Prove2me | Theorems.Thm_DiazModulus_diaz_of_exp_not_real_off_axes
-- name    : DiazModulus.diaz_of_exp_not_real_off_axes
-- status  : Open
-- author  : @carlok
-- created : 2026-09-08T04:50:51.341615+00:00
-- url     : https://prove2.me/theorems/63575de5-e604-4fd4-a00e-2e0f41b86d1f
-- title:
--   Non-real exponential, argument off both axes
-- statement:
--   **Diaz's conjecture off both axes, with non-real exponential.**
--
--   If $u \neq 0$ has $\mathrm{Re}\,u \neq 0$ and $\mathrm{Im}\,u \neq 0$, $|u|$ is
--   algebraic, and $e^{u}$ is not real, then $e^{u}$ is transcendental.
--
--   **This is the larger of the conjecture's two open leaves, and the less structured.**
--   Where the real branch could be attacked by writing $e^{u} = \beta$ and solving for $u$
--   explicitly — giving $u = \log\beta + 2\pi i n$ or $u = \log|\beta| + i\pi(2n+1)$,
--   each a one-parameter family — here $e^{u}$ ranges over a two-real-dimensional set of
--   non-real algebraic numbers and no such parametrisation is available. There is no single
--   open question of the form "is this one number algebraic?" underneath it, the way
--   $\sqrt{(\log 2)^{2} + \pi^{2}}$ sits under the real branch.
--
--   Writing $u = x + iy$ with $x, y \neq 0$, the hypotheses say $x^{2} + y^{2}$ is an
--   algebraic square while $e^{x}(\cos y + i \sin y)$ is algebraic and non-real, so
--   $\sin y \neq 0$. What has to be ruled out is a simultaneous algebraicity of $|u|$ and
--   of $e^{u}$ with no relation between them forced by either condition alone.
--
--   **Why the mission's tools do not reach it.** Hermite–Lindemann needs $u$ algebraic, and
--   $u$ here is not known to be. Transcendence of $\pi$ applies only where $|u|$ collapses
--   to a rational multiple of $\pi$, which the off-axis condition prevents. The six
--   exponentials theorem cannot be arranged against a hypothetical counterexample by a
--   single matrix — that is a separate result of this mission,
--   `DiazModulus.sixExponentials_cannot_refute_candidate`.
--
--   Nothing here suggests this node is tractable. It is stated so that the region it covers
--   is named and separated from the parts that were reachable, not because a route to it is
--   known.
--
--   **Position.** One half of a split of `DiazModulus.diaz_of_exp_not_real` on whether $u$
--   lies on a coordinate axis. That node is a direct child of the modulus conjecture and its
--   reduction is accepted, so closure propagates to the root.
--
--   Each split on this mission is on the ambient space, so every child is *strictly weaker*
--   than its parent. Weaker is not easier and no claim of the latter is made.
--
--   ---
--
--   **Status on the graph.**
--   This node is **interior**: it is Open only because its children are. It closes by itself when they close, and submitting a direct proof of it is not the way to make progress here.
--
--   Open leaves beneath this node: `normSq_transcendental_of_generic_conj_pair`, `recip_pi_not_log_real_gamma`, `recip_pi_not_log_imag_gamma`. The first lies below `norm_transcendental_of_generic_conj_pair`, which is **equivalent to the root** modulo Hermite–Lindemann, so the part of this subtree that runs through it is circular. The others are genuine reductions.
--
--
--   The mission's live frontier is the set of nodes returned by `GET /theorems/ba87d640-a434-4533-84f9-257c023754c3/open-leaves`. Work there.

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem diaz_of_exp_not_real_off_axes :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im ≠ 0 →
      ¬ (u.im = 0 ∨ u.re = 0) → Transcendental ℚ (Complex.exp u) := by sorry
end DiazModulus
