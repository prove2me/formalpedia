-- Prove2me | Theorems.Thm_DiazModulus_diaz_of_exp_real_self_not_real
-- name    : DiazModulus.diaz_of_exp_real_self_not_real
-- status  : Open
-- author  : @carlok
-- created : 2026-09-08T04:08:09.572685+00:00
-- url     : https://prove2.me/theorems/22d18ab5-38f0-4d6a-a0c0-9c5da4089404
-- title:
--   Real exponential, non-real argument
-- statement:
--   **Diaz's conjecture when $e^{u}$ is real and $u$ is not.**
--
--   If $u \neq 0$ is non-real, $|u|$ is algebraic, and $e^{u}$ is real, then $e^{u}$ is
--   transcendental.
--
--   **This is where the content of the real branch sits.** Write $e^{u} = \beta$, real and
--   algebraic. For $\beta > 0$ the solutions are $u = \log\beta + 2\pi i n$, and $u$
--   non-real forces $n \neq 0$; for $\beta < 0$ they are $u = \log|\beta| + i\pi(2n+1)$,
--   where $u$ is non-real automatically. So the statement asserts that neither
--   $$(\log\beta)^{2} + 4\pi^{2}n^{2} \quad (n \neq 0)
--   \qquad\text{nor}\qquad
--   (\log|\beta|)^{2} + \pi^{2}(2n+1)^{2}$$
--   is the square of an algebraic number, for any real algebraic $\beta$ of the relevant
--   sign.
--
--   Its smallest instance takes $\beta = -2$, $n = 0$, and asks whether
--   $\sqrt{(\log 2)^{2} + \pi^{2}}$ — the modulus of the principal logarithm of $-2$ — is
--   algebraic. That single question is open, and a proof of it would not settle this node,
--   only one point of it.
--
--   **No claim that this is easier.** It is strictly weaker than its parent and unknown.
--   Its sibling `DiazModulus.diaz_of_exp_real_self_real` is closable from results the
--   mission already has, which is precisely why the two were separated.
--
--   **Position.** This is one half of a split of `DiazModulus.diaz_of_exp_real` on whether
--   $u$ itself is real. That node is in turn one half of a split of the modulus conjecture
--   on whether $e^{u}$ is real, and the reduction to the conjecture is already accepted, so
--   closing this and its sibling closes `diaz_of_exp_real`, and closing that and *its*
--   sibling closes the conjecture.
--
--   Each split is on the ambient space, so every child is *strictly weaker* than its parent
--   rather than a restatement of it.
--
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
theorem diaz_of_exp_real_self_not_real :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im = 0 →
      u.im ≠ 0 → Transcendental ℚ (Complex.exp u) := by sorry
end DiazModulus
