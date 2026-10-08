-- Prove2me | Theorems.Thm_FixpNash_WeakApprox_eps_nash_is_weak_fixed_point
-- name    : FixpNash.WeakApprox.eps_nash_is_weak_fixed_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:44:09.787818+00:00
-- url     : https://prove2.me/theorems/512661e6-6991-4a16-a08e-360141c8b5d3
-- title:
--   Proof of Proposition 3, p. 20 — an ε′/(n+1)-NE is a weak ε′-approximate fixed point of Nash's function
-- statement:
--   Let $\Gamma$ be a finite game, let $n$ be the maximum number of pure strategies of a player, and let $F_\Gamma$ be Nash's function. Let $\varepsilon'>0$ and put $\varepsilon=\varepsilon'/(n+1)$. If $x$ is an $\varepsilon$-Nash equilibrium of $\Gamma$, then $x$ is a weak $\varepsilon'$-approximate fixed point of $F_\Gamma$: $x$ is a mixed profile and
--   $$|F_\Gamma(x)_{(i,j)}-x_{i,j}|<\varepsilon'\qquad\text{for every player } i \text{ and every } j\in S_i.$$
--
--   This is the first direction of the proof of Proposition 3: an $\varepsilon$-NE is almost fixed by Nash's function, with a tolerance $\varepsilon'$ only a factor $n+1$ larger than $\varepsilon$.
--
--   **Formalization Note** The proof on p. 20 ends with "$\le(m_i+1)\epsilon\le\epsilon'$. Therefore, $x$ is a weak $\epsilon'$-approximate fixed point", and the weak approximation of p. 16 is strict. The theorem states the page's conclusion, the strict weak approximation (`IsWeakApproxFixedPoint`); it holds with the printed $\varepsilon=\varepsilon'/(n+1)$, since every coordinate of $F_\Gamma(x)-x$ is at most $n\varepsilon=n\varepsilon'/(n+1)<\varepsilon'$ in absolute value. The page's $m_i$ is $|S_i|\le n$. $n$ is computed from the game (`maxNumStrategies`); the $\varepsilon$-NE is the published `IsEpsApproxNash`, which includes that $x$ is a mixed profile.
-- source:
--   Etessami & Yannakakis, On the complexity of Nash equilibria and other fixed points, author manuscript (SIAM J. Comput. 39 (2010)), proof of Proposition 3, first direction, p. 20

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_NashMap_nashMap
import Definitions.Def_DGPNash_WellSupported_Equilibria
import Definitions.Def_FixpNash_WeakApprox_NashFunction
import Definitions.Def_FixpNash_WeakApprox_GameConstants

namespace FixpNash.WeakApprox

/-- Proof of Proposition 3, first direction (p. 20): with `n` the maximum number of pure
strategies of a player, an `ε'/(n+1)`-NE `x` is a weak `ε'`-approximate fixed point of Nash's
function, i.e. `x ∈ D_Γ` and `|F_Γ(x)_{(i,j)} - x_{i,j}| < ε'` for all `i, j`. -/
theorem eps_nash_is_weak_fixed_point {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (ε' : ℝ) (hε' : 0 < ε') (x : ∀ i, S i → ℝ)
    (hx : DGPNash.WellSupported.IsEpsApproxNash u x (ε' / ((maxNumStrategies S : ℝ) + 1))) :
    IsWeakApproxFixedPoint u x ε' := by sorry

end FixpNash.WeakApprox
