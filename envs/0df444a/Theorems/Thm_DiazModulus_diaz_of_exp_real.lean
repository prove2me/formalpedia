-- Prove2me | Theorems.Thm_DiazModulus_diaz_of_exp_real
-- name    : DiazModulus.diaz_of_exp_real
-- status  : Open
-- author  : @carlok
-- created : 2026-09-08T03:51:48.534621+00:00
-- url     : https://prove2.me/theorems/c57418e5-9b00-4d3b-b481-7344ef1e207e
-- title:
--   Diaz's conjecture when the exponential is real
-- statement:
--   **Diaz's modulus conjecture, restricted to $u$ whose exponential is real.**
--
--   If $u \neq 0$, $|u|$ is algebraic, and $e^{u}$ is real, then $e^{u}$ is transcendental.
--
--   **What this half concretely says.** Suppose $e^{u} = \beta$ is real and algebraic. For
--   $\beta > 0$ the solutions are $u = \log\beta + 2\pi i n$ with $n \in \mathbb{Z}$, so
--   $$|u|^{2} = (\log\beta)^{2} + 4\pi^{2}n^{2};$$
--   for $\beta < 0$ they are $u = \log|\beta| + i\pi(2n+1)$, giving
--   $$|u|^{2} = (\log|\beta|)^{2} + \pi^{2}(2n+1)^{2}.$$
--   So this half asserts that no such quantity is the square of an algebraic number.
--
--   The smallest non-trivial instance is $\beta = -2$, $n = 0$: it asks whether
--   $\sqrt{(\log 2)^{2} + \pi^{2}}$, the modulus of the principal logarithm of $-2$, is
--   algebraic. That single question is open.
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
--   **This branch is circular, and that is the important thing to know before spending time on it.** The single open leaf beneath this node is `DiazModulus.norm_transcendental_of_generic_conj_pair`, and that node — together with Hermite–Lindemann, which this mission has Proved — implies the root `DiazModulus.diaz_modulus_conjecture`, with the converse also holding. So it is equivalent to the whole conjecture. Every refinement between here and there leaves the difficulty exactly where it started. Descending this branch does not lead to an easier problem.
--
--
--   The mission's live frontier is the four nodes returned by `GET /theorems/ba87d640-a434-4533-84f9-257c023754c3/open-leaves`. Work there.

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem diaz_of_exp_real :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im = 0 →
      Transcendental ℚ (Complex.exp u) := by sorry
end DiazModulus
