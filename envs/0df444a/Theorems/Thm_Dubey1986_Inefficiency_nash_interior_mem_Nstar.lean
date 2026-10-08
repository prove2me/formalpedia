-- Prove2me | Theorems.Thm_Dubey1986_Inefficiency_nash_interior_mem_Nstar
-- name    : Dubey1986.Inefficiency.nash_interior_mem_Nstar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:35:30.682991+00:00
-- url     : https://prove2.me/theorems/4e0542b2-ff44-4d66-87a3-372dcd77f06d
-- title:
--   p. 4, (i) — at an interior Nash equilibrium each player's own partial derivatives vanish
-- statement:
--   Let $n\ge2$, $k(i)\ge1$, let $V^i\supseteq S^i$ be open, and let $u\in(U)^n$ be a game. If $s=(s^1,\dots,s^n)$ is a Nash equilibrium of $u$ and every $s^i$ lies in the interior of $S^i$, then
--   $$D_u(s)\in N^*,$$
--   that is, $\partial u^i/\partial x_j(s)=0$ for every player $i$ and every coordinate $j$ of player $i$'s own block.
--
--   This is step (i) of the proof of the main theorem: it places the interior Nash equilibria inside $D_u^{-1}(N^*)$.
--
--   **Formalization Note** The interiority of every $s^i$ is the standing case assumption of the first part of the proof ("First we focus on the case when $s^i$ is in the interior of $S^i$", p. 3).
-- source:
--   Dubey, Inefficiency of Nash Equilibria, IIASA WP-83-74 (July 1983), p. 4, display (i) (under the case assumption of p. 3, Proof, first sentence)

import Mathlib
import Definitions.Def_Dubey1986_Inefficiency_Setting
import Definitions.Def_Dubey1986_Inefficiency_Derivative

namespace Dubey1986.Inefficiency

theorem nash_interior_mem_Nstar {n : ℕ} (hn : 2 ≤ n) (k : Fin n → ℕ) (hk : ∀ i, 1 ≤ k i)
    (V : ∀ i, Set (Fin (k i) → ℝ)) (hVo : ∀ i, IsOpen (V i))
    (hSV : ∀ i, simplex (k i) ⊆ V i) (u : Fin n → Strat k → ℝ) (hu : IsGame V u)
    (s : Strat k) (hint : ∀ i, s i ∈ interior (simplex (k i))) (hs : s ∈ NashSet u) :
    Dmap u s ∈ Nstar k := by sorry

end Dubey1986.Inefficiency
