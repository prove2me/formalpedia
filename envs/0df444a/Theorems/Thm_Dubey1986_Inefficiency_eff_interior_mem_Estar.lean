-- Prove2me | Theorems.Thm_Dubey1986_Inefficiency_eff_interior_mem_Estar
-- name    : Dubey1986.Inefficiency.eff_interior_mem_Estar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:37:12.514686+00:00
-- url     : https://prove2.me/theorems/f3e8d2ad-011e-4587-af54-fb1728b2cd1c
-- title:
--   p. 4, (ii) — at an interior efficient point the payoff gradients are linearly dependent
-- statement:
--   Let $n\ge2$, $k(i)\ge1$, let $V^i\supseteq S^i$ be open, and let $u\in(U)^n$ be a game. If $s$ is an efficient point of $u$ and every $s^i$ lies in the interior of $S^i$, then
--   $$D_u(s)\in E^*,$$
--   that is, the derivatives $Du^1(s),\dots,Du^n(s)$ are linearly dependent.
--
--   This is step (ii) of the proof, the necessary condition for Pareto optimality pointed out by Smale; together with (i) it places interior efficient Nash equilibria in $D_u^{-1}(N^*\cap E^*)$.
--
--   **Formalization Note** The interiority of every $s^i$ is the standing case assumption of the first part of the proof (p. 3). Only this direction of the Appendix's characterization is used and stated.
-- source:
--   Dubey, Inefficiency of Nash Equilibria, IIASA WP-83-74 (July 1983), p. 4, display (ii) (under the case assumption of p. 3, Proof, first sentence)

import Mathlib
import Definitions.Def_Dubey1986_Inefficiency_Setting
import Definitions.Def_Dubey1986_Inefficiency_Derivative

namespace Dubey1986.Inefficiency

theorem eff_interior_mem_Estar {n : ℕ} (hn : 2 ≤ n) (k : Fin n → ℕ) (hk : ∀ i, 1 ≤ k i)
    (V : ∀ i, Set (Fin (k i) → ℝ)) (hVo : ∀ i, IsOpen (V i))
    (hSV : ∀ i, simplex (k i) ⊆ V i) (u : Fin n → Strat k → ℝ) (hu : IsGame V u)
    (s : Strat k) (hint : ∀ i, s i ∈ interior (simplex (k i))) (hs : s ∈ EffSet u) :
    Dmap u s ∈ Estar k := by sorry

end Dubey1986.Inefficiency
