-- Prove2me | Theorems.Thm_DiazModulus_diaz_of_exp_not_real
-- name    : DiazModulus.diaz_of_exp_not_real
-- status  : Open
-- author  : @carlok
-- created : 2026-09-08T03:51:56.817686+00:00
-- url     : https://prove2.me/theorems/a8b88767-c52e-4166-8a4c-d00348616caa
-- title:
--   Diaz's conjecture when the exponential is not real
-- statement:
--   **Diaz's modulus conjecture, restricted to $u$ whose exponential is not real.**
--
--   If $u \neq 0$, $|u|$ is algebraic, and $e^{u}$ is not real, then $e^{u}$ is
--   transcendental.
--
--   This is the complementary half to `DiazModulus.diaz_of_exp_real`. It is the larger of
--   the two in the sense that $e^{u}$ ranges over a two-real-dimensional set rather than a
--   one-dimensional one, and correspondingly it has no reduction to a single-variable
--   question of the kind available on the real side.
--
--   Note that the mission's proved `DiazModulus.diaz_on_axes_of_hermite_lindemann` settles
--   neither half: it constrains $u$ by lying on an axis, not $e^{u}$ by being real.
--
--   **Role.** This is one half of a case split on `\mathrm{Im}\,e^{u}`. Together with its
--   sibling it gives Diaz's modulus conjecture, and the reduction is submitted against the
--   conjecture, so closing both halves closes the conjecture.
--
--   Unlike a necessary condition on a hypothetical counterexample, each half is a *strictly
--   weaker* statement than the conjecture: it quantifies over a proper subclass of $u$. A
--   statement of the form "every counterexample satisfies $\Phi$" cannot decompose an
--   assertion that no counterexample exists — if $\Phi$ is provably necessary the residual
--   is equivalent to the original, and otherwise it is conjecturally vacuous. A split on the
--   ambient space is the shape that avoids this.
--
--   **Honesty about difficulty.** No claim is made that this half is *easier*, only that it
--   is strictly weaker and concretely phrasable. Neither half is known.
--
--
--   ---
--
--   **Status on the graph.**
--   This node is **interior**: it is Open only because its children are. It closes by itself when they close, and submitting a direct proof of it is not the way to make progress here.
--
--   Open leaves beneath this node: `norm_transcendental_of_generic_conj_pair`, `recip_pi_not_log_real_gamma`, `four_exponentials_trdeg_one`, `recip_pi_not_log_imag_gamma`. One of them, `norm_transcendental_of_generic_conj_pair`, is **equivalent to the root** modulo Hermite–Lindemann, so the part of this subtree that runs through it is circular. The others are genuine reductions.
--
--
--   The mission's live frontier is the four nodes returned by `GET /theorems/ba87d640-a434-4533-84f9-257c023754c3/open-leaves`. Work there.

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem diaz_of_exp_not_real :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im ≠ 0 →
      Transcendental ℚ (Complex.exp u) := by sorry
end DiazModulus
