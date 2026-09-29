-- Prove2me | Theorems.Thm_DiazModulus_diaz_of_exp_real_generic
-- name    : DiazModulus.diaz_of_exp_real_generic
-- status  : Open
-- author  : @carlok
-- created : 2026-09-08T04:41:14.923606+00:00
-- url     : https://prove2.me/theorems/813352be-5c64-4e5a-b973-825a07d50640
-- title:
--   The generic real case: both parts of u non-zero
-- statement:
--   **Diaz's conjecture where both parts of $u$ are non-zero and $e^{u}$ is real.**
--
--   If $u \neq 0$ has $\mathrm{Re}\,u \neq 0$ and $\mathrm{Im}\,u \neq 0$, $|u|$ is
--   algebraic, and $e^{u}$ is real and $\neq 1$, then $e^{u}$ is transcendental.
--
--   **This is the core of the real branch, with every degenerate corner removed.** Write
--   $e^{u} = \beta$, real and algebraic. Then $\mathrm{Re}\,u = \log|\beta| \neq 0$, so
--   $|\beta| \neq 1$, and $\mathrm{Im}\,u \neq 0$. The two families are
--
--   $$u = \log\beta + 2\pi i n \quad (\beta > 0,\ \beta \neq 1,\ n \neq 0),
--   \qquad
--   u = \log|\beta| + i\pi(2n+1) \quad (\beta < 0,\ \beta \neq -1),$$
--
--   and the claim is that
--
--   $$(\log\beta)^{2} + 4\pi^{2}n^{2}
--   \qquad\text{and}\qquad
--   (\log|\beta|)^{2} + \pi^{2}(2n+1)^{2}$$
--
--   are never squares of algebraic numbers. **Both terms are now genuinely non-zero** — that
--   is what distinguishes this node from the three siblings already closed above it, each of
--   which died because one term vanished and the surviving one was a rational multiple of
--   $\pi$ or an algebraic number outright.
--
--   The smallest instance takes $\beta = -2$, $n = 0$: is
--   $\sqrt{(\log 2)^{2} + \pi^{2}}$ — the modulus of the principal logarithm of $-2$ —
--   algebraic? That single question is open, and answering it would settle one point of this
--   node rather than the node.
--
--   **Why it is hard, stated honestly.** A sum of two independent transcendental
--   contributions is exactly the configuration Diaz's own partial results do not reach, and
--   transcendence of $\pi$, Hermite–Lindemann and the six exponentials theorem — all
--   available on this mission — do not touch it. Nothing here suggests this node is
--   tractable; it is where the conjecture's difficulty actually lives, isolated so that the
--   easy parts no longer obscure it.
--
--   **Position.** One half of a split of `DiazModulus.diaz_of_exp_ne_one` on whether
--   $\mathrm{Re}\,u = 0$. That node sits under `diaz_of_exp_real_self_not_real`, under
--   `diaz_of_exp_real`, under the modulus conjecture, and every reduction in that chain is
--   already accepted, so closure propagates to the root.
--
--   Each split on this mission is on the ambient space, so every child is *strictly weaker*
--   than its parent. Weaker is not easier and no claim of the latter is made.
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
theorem diaz_of_exp_real_generic :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im = 0 →
      u.im ≠ 0 → Complex.exp u ≠ 1 → u.re ≠ 0 →
      Transcendental ℚ (Complex.exp u) := by sorry
end DiazModulus
