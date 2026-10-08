-- Prove2me | Theorems.Thm_FixpNash_WeakApprox_proposition_3
-- name    : FixpNash.WeakApprox.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:44:22.191026+00:00
-- url     : https://prove2.me/theorems/d4c7beca-6cc5-42c3-89e7-542d35507881
-- title:
--   Proposition 3 — ε-NE and weak approximate fixed points of Nash's function, with the explicit ε′ of the proof
-- statement:
--   Let $\Gamma$ be a finite game in normal form in which every player has at least one pure strategy. Let $n$ be the maximum number of pure strategies of a player, $M$ the maximum, over all players $i$, of the difference between the maximum and the minimum payoff of player $i$ under any pure strategy profile, and $c=1+M$. Let $F_\Gamma$ be Nash's function. Then:
--
--   1. for every $\varepsilon'>0$, every $\varepsilon'/(n+1)$-Nash equilibrium $x$ of $\Gamma$ is a weak $\varepsilon'$-approximate fixed point of $F_\Gamma$, i.e.
--   $$|F_\Gamma(x)_{(i,j)}-x_{i,j}|<\varepsilon'\qquad\text{for all } i \text{ and } j\in S_i;$$
--   2. for every $\varepsilon$ with $0<\varepsilon\le1$, every weak $\varepsilon'$-approximate fixed point of $F_\Gamma$ with
--   $$\varepsilon'=\frac{\varepsilon^2}{4c^2n^3}$$
--   (a mixed profile $x$ with $|F_\Gamma(x)-x|_\infty<\varepsilon'$) is an $\varepsilon$-Nash equilibrium of $\Gamma$.
--
--   The paper states Proposition 3 as a complexity statement: "Computing an $\epsilon$-NE (for a given game, $\Gamma$, and given $\epsilon>0$) is P-time equivalent to computing a weak $\epsilon'$-approximate fixed point of Nash's function (for a given instance of Nash's function, $F_\Gamma$, and given $\epsilon'>0$)." Its proof establishes the two implications above, with the explicit tolerances $\varepsilon'/(n+1)$ and $\varepsilon^2/(4c^2n^3)$, whose encoding sizes are polynomial in those of the game and the tolerance; the P-time equivalence follows from them. Together with the polynomial continuity of Nash's function, the result places the computation of $\varepsilon$-NE in PPAD.
--
--   **Formalization Note** The "P-time equivalence" is formalized through the two explicit implications of the proof, not as a statement about algorithms. Part 1 concludes, as the page does, that $x$ is a weak $\epsilon'$-approximate fixed point (strict, as defined on p. 16); the computation on p. 20 prints the looser bound "$\le(m_i+1)\epsilon\le\epsilon'$", but the strict bound holds with the same $\varepsilon'/(n+1)$. Part 2 assumes $\varepsilon\le1$, as the page does "without loss of generality" (an $\varepsilon$-NE for $\varepsilon=1$ is an $\varepsilon$-NE for every larger $\varepsilon$). $n$, $M$, $c$ are computed from the game. Payoffs are real rather than rational. The $\varepsilon$-NE is the published `IsEpsApproxNash`.
-- source:
--   Etessami & Yannakakis, On the complexity of Nash equilibria and other fixed points, author manuscript (SIAM J. Comput. 39 (2010)), Proposition 3 and its proof, pp. 20–21

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_NashMap_nashMap
import Definitions.Def_DGPNash_WellSupported_Equilibria
import Definitions.Def_FixpNash_WeakApprox_NashFunction
import Definitions.Def_FixpNash_WeakApprox_GameConstants

namespace FixpNash.WeakApprox

/-- Proposition 3 (p. 20) in the explicit form of its proof (pp. 20–21). Let `n` be the maximum
number of pure strategies of a player, `M` the maximum over players of the spread of their pure
payoffs, and `c = 1 + M`.
(A) For every `ε' > 0`, every `ε'/(n+1)`-NE `x` is a weak `ε'`-approximate fixed point of Nash's
function.
(B) For every `0 < ε ≤ 1`, every weak `ε²/(4c²n³)`-approximate fixed point of Nash's function
is an `ε`-NE. -/
theorem proposition_3 {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (hS : ∀ i, Nonempty (S i)) (u : ι → (∀ i, S i) → ℝ) :
    (∀ ε' : ℝ, 0 < ε' → ∀ x : ∀ i, S i → ℝ,
        DGPNash.WellSupported.IsEpsApproxNash u x (ε' / ((maxNumStrategies S : ℝ) + 1)) →
          IsWeakApproxFixedPoint u x ε') ∧
      (∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x : ∀ i, S i → ℝ,
        IsWeakApproxFixedPoint u x
            (ε ^ 2 / (4 * cConst u ^ 2 * (maxNumStrategies S : ℝ) ^ 3)) →
          DGPNash.WellSupported.IsEpsApproxNash u x ε) := by sorry

end FixpNash.WeakApprox
