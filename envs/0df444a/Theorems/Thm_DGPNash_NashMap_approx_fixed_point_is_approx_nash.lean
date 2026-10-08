-- Prove2me | Theorems.Thm_DGPNash_NashMap_approx_fixed_point_is_approx_nash
-- name    : DGPNash.NashMap.approx_fixed_point_is_approx_nash
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T10:05:25.365664+00:00
-- url     : https://prove2.me/theorems/deab3dfc-4f50-4eb1-8814-2460816cb7a5
-- title:
--   Lemma 3.8 — approximate fixed points are approximate Nash equilibria
-- statement:
--   Consider a normal-form game of $r\ge2$ players with the same nonempty set of $n$ pure strategies and nonnegative payoff entries. Let $U_{\max}$ be the largest payoff entry and let $f$ be Nash's map. If a mixed profile $x$ satisfies $\|f(x)-x\|_\infty\le\varepsilon'$ for $\varepsilon'\ge0$, then $x$ is an approximate Nash equilibrium with error
--
--   $$n\sqrt{\varepsilon'(1+nU_{\max})}\bigl(1+\sqrt{\varepsilon'(1+nU_{\max})}\bigr)\max\{U_{\max},1\}.$$
--
--   Thus every player's expected gain from any unilateral mixed-strategy deviation is at most this quantity. The bound connects numerical approximation of a fixed point to approximation of a Nash equilibrium.
--
--   **Formalization Note** Lemma 3.8 writes $x\in\mathbb R^{n\cdot r}$, but its proof and the definition of approximate Nash equilibrium require $x$ to lie in the product of simplices; this is made explicit. The infinity-norm condition is coordinatewise, and the paper's one-based indices are `Fin` indices.
-- source:
--   Daskalakis, Goldberg & Papadimitriou, The Complexity of Computing a Nash Equilibrium, SIAM J. Comput. 39(1):195–259 (2009), pp. 207–209, Lemma 3.8; https://doi.org/10.1137/070699652

import Definitions.Def_DGPNash_NashMap_nashMap

namespace DGPNash.NashMap

/-- Lemma 3.8, p. 207: an approximate fixed point of Nash's map is an approximate Nash equilibrium. -/
theorem approx_fixed_point_is_approx_nash {r n : ℕ} (hr : 2 ≤ r) (hn : 0 < n)
    (u : Fin r → (Fin r → Fin n) → ℝ) (hu : ∀ p s, 0 ≤ u p s)
    (x : Fin r → Fin n → ℝ) (hx : AGT.IsMixedProfile x)
    (ε' : ℝ) (hε' : 0 ≤ ε')
    (hclose : ∀ p j, |nashMap u x p j - x p j| ≤ ε') :
    IsApproxNash u x
      ((n : ℝ) * Real.sqrt (ε' * (1 + (n : ℝ) * maxPayoff u)) *
        (1 + Real.sqrt (ε' * (1 + (n : ℝ) * maxPayoff u))) *
        max (maxPayoff u) 1) := by sorry

end DGPNash.NashMap
