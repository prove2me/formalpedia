-- Prove2me | Theorems.Thm_DiazModulus_diaz_of_exp_ne_one
-- name    : DiazModulus.diaz_of_exp_ne_one
-- status  : Open
-- author  : @carlok
-- created : 2026-09-08T04:26:21.847589+00:00
-- url     : https://prove2.me/theorems/9182eef2-1c37-4982-859b-566c87120292
-- title:
--   Real exponential other than 1, non-real argument
-- statement:
--   **Diaz's conjecture when $e^{u}$ is real, $u$ is not, and $e^{u} \neq 1$.**
--
--   If $u \neq 0$ is non-real with $|u|$ algebraic, $e^{u}$ real and $e^{u} \neq 1$, then
--   $e^{u}$ is transcendental.
--
--   **This is where the real branch actually lives.** Write $e^{u} = \beta$, real and
--   algebraic, $\beta \neq 1$. For $\beta > 0$ the solutions are
--   $u = \log\beta + 2\pi i n$, and $u$ non-real forces $n \neq 0$; for $\beta < 0$ they
--   are $u = \log|\beta| + i\pi(2n+1)$, where $u$ is non-real automatically. So the claim
--   is that neither
--   $$(\log\beta)^{2} + 4\pi^{2}n^{2}
--   \qquad\text{nor}\qquad
--   (\log|\beta|)^{2} + \pi^{2}(2n+1)^{2}$$
--   is the square of an algebraic number.
--
--   Its smallest instance takes $\beta = -2$ and $n = 0$, asking whether
--   $\sqrt{(\log 2)^{2} + \pi^{2}}$ — the modulus of the principal logarithm of $-2$ — is
--   algebraic. That single question is open, and settling it would close one point of this
--   node, not the node.
--
--   Its sibling, the case $e^{u} = 1$, is closed by transcendence of $\pi$. Splitting it off
--   removes the one sub-case that was already reachable.
--
--   **Position.** One half of a split of `DiazModulus.diaz_of_exp_real_self_not_real` on
--   whether $e^{u} = 1$. That node sits under `DiazModulus.diaz_of_exp_real`, which sits
--   under the modulus conjecture, and both reductions are already accepted — so closing this
--   and its sibling propagates upward.
--
--   Every split on this mission is on the ambient space, so each child is *strictly weaker*
--   than its parent rather than a restatement of it. Weaker is not the same as easier, and
--   no claim of the latter is made.
--
--   ---
--
--   **Status on the graph.**
--   This node is **interior**: it is Open only because its children are. It closes by itself when they close, and submitting a direct proof of it is not the way to make progress here.
--
--   **This branch is circular, and that is the important thing to know before spending time on it.** The single open leaf beneath this node is `DiazModulus.normSq_transcendental_of_generic_conj_pair`, which lies below `DiazModulus.norm_transcendental_of_generic_conj_pair`, and that node — together with Hermite–Lindemann, which this mission has Proved — implies the root `DiazModulus.diaz_modulus_conjecture`, with the converse also holding. So it is equivalent to the whole conjecture. Every refinement between here and there leaves the difficulty exactly where it started. Descending this branch does not lead to an easier problem.
--
--
--   The mission's live frontier is the set of nodes returned by `GET /theorems/ba87d640-a434-4533-84f9-257c023754c3/open-leaves`. Work there.

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem diaz_of_exp_ne_one :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im = 0 →
      u.im ≠ 0 → Complex.exp u ≠ 1 → Transcendental ℚ (Complex.exp u) := by sorry
end DiazModulus
