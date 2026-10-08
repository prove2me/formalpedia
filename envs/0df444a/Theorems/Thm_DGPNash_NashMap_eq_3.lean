-- Prove2me | Theorems.Thm_DGPNash_NashMap_eq_3
-- name    : DGPNash.NashMap.eq_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T10:05:08.854175+00:00
-- url     : https://prove2.me/theorems/fc7480ba-1039-4513-971a-f5016730c087
-- title:
--   Eq. (3) — approximate fixedness bounds total gain
-- statement:
--   Let $x$ be a mixed profile in a game with nonnegative payoffs, and let every coordinate of $f(x)-x$ have absolute value at most $\varepsilon'\ge0$. Put $\varepsilon''=\varepsilon'(1+nU_{\max})$. For each player $p$ and strategy $j$,
--
--   $$x^p_j\sum_{i\in[n]}B^p_i(x)\le B^p_j(x)+\varepsilon''.$$
--
--   This is the displayed inequality (3) at the start of Lemma 3.8's case analysis. **Formalization Note** $U_{\max}$ is the game's actual largest payoff entry, and $B^p_j$ is the positive part of the pure-strategy advantage over the current expected payoff.
-- source:
--   Daskalakis, Goldberg & Papadimitriou, The Complexity of Computing a Nash Equilibrium, SIAM J. Comput. 39(1):195–259 (2009), p. 208, §3.2 Eq. (3); https://doi.org/10.1137/070699652

import Definitions.Def_DGPNash_NashMap_nashMap

namespace DGPNash.NashMap

open Finset

/-- Equation (3), p. 208: a coordinatewise consequence of approximate fixedness. -/
theorem eq_3 {r n : ℕ} (hr : 2 ≤ r) (hn : 0 < n)
    (u : Fin r → (Fin r → Fin n) → ℝ) (hu : ∀ p s, 0 ≤ u p s)
    (x : Fin r → Fin n → ℝ) (hx : AGT.IsMixedProfile x)
    (ε' : ℝ) (hε' : 0 ≤ ε')
    (hclose : ∀ p j, |nashMap u x p j - x p j| ≤ ε') :
    ∀ p j, x p j * (∑ i : Fin n, gain u x p i) ≤
      gain u x p j + ε' * (1 + (n : ℝ) * maxPayoff u) := by sorry

end DGPNash.NashMap
