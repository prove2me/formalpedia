-- Prove2me | Theorems.Thm_Aumann1974_ZeroSum_zero_sum_both_exceed_value
-- name    : Aumann1974.ZeroSum.zero_sum_both_exceed_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:08:39.676363+00:00
-- url     : https://prove2.me/theorems/8a1982f1-4c2a-4ff0-a890-0aef29a64fdc
-- title:
--   Proposition 6.1 — subjective events let both players of a zero-sum game beat the value
-- statement:
--   Let $G$ be a two-person zero-sum game: finite pure strategy sets $S_1,S_2$, a finite outcome set $X$, an outcome function $g:S_1\times S_2\to X$ onto $X$, and utilities with $u_1(x)+u_2(x)=0$ for all $x$. Let $v$ be its **value** (player 1's payoff at a Nash equilibrium of the mixed extension, unique by the minimax theorem). Let $(\Omega,\mathcal B,\mathcal J_1,\mathcal J_2,p_1,p_2)$ be a randomizing structure satisfying Assumption II. Assume
--
--   1. (6.2) there are outcomes $x,y\in X$ with $u_1(x) > v > u_1(y)$;
--   2. (6.3) for each player $i$ there is a subjective event $B_i$ regarding which $i$ is informed: $B_i\in\mathcal J_i$ and $p_1(B_i)\ne p_2(B_i)$.
--
--   Then there is a pair $s=(s_1,s_2)$ of strategies ($s_i$ measurable with respect to $\mathcal J_i$) such that
--   $$H_1(s) > v,\qquad H_2(s) > -v,$$
--   where $H_i(s)=\int_\Omega u_i(g(s(\omega)))\,dp_i(\omega)$ is computed under player $i$'s own subjective probability $p_i$.
--
--   In a zero-sum game with objective randomization no pair of strategies can give both players more than their security levels $v$ and $-v$. The proposition shows that as soon as each player has access to an event on whose probability the players disagree, there is an agreement that each player, by his own beliefs, strictly prefers to playing the game: subjectivity alone makes zero-sum games "positive-sum". The paper also shows (p. 81) that (6.3) cannot be weakened to a subjective event of which only one player is informed.
--
--   **Formalization Note** Players $1,2$ are `0, 1 : Fin 2`. The pair $s$ is not required to be an equilibrium point. The value is pinned through `AGT.IsMixedNash` of the published definition `agt_games`, not left free. Assumption II is the paper's standing assumption. The paper calls this result "Proposition 6.5" on p. 81 (misprint).
-- source:
--   R. J. Aumann, Subjectivity and Correlation in Randomized Strategies, J. Math. Econ. 1 (1974) 67–96, https://doi.org/10.1016/0304-4068(74)90037-8, Sect. 6, p. 80 (PDF p. 14), Proposition 6.1, conditions (6.2)–(6.4); value defined p. 79 (PDF p. 13); proof pp. 80–81 (PDF pp. 14–15)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_Aumann1974_ZeroSum_RandomizingStructure
import Definitions.Def_Aumann1974_ZeroSum_Payoffs

namespace Aumann1974.ZeroSum

open MeasureTheory

/-- **Proposition 6.1** (Aumann 1974, *Subjectivity and Correlation in Randomized Strategies*,
J. Math. Econ. 1, p. 80, PDF p. 14): let `G` be a 2-person 0-sum game with value `v`. Assume
(6.2) there are outcomes `x` and `y` with `u₁(x) > v > u₁(y)`;
(6.3) for each player `i`, there is a subjective event `Bᵢ` regarding which `i` is informed.
Then there is a pair `s` of strategies such that
(6.4) `H₁(s) > v`, `H₂(s) > −v`.

**Formalization Note.** Players `1, 2` are `0, 1 : Fin 2`; `S 0`, `S 1` and `X` are finite, `g`
is onto `X` and `u` is the adopted zero-sum pair of utilities (`IsZeroSum`). `v` is **the value**
(`IsValue`: player 1's payoff at a Nash equilibrium of the mixed extension, which by the minimax
theorem is unique), not a free real. Assumption II (standing assumption, p. 75) is a hypothesis.
(6.3) is required of **both** players: `Bᵢ ∈ 𝒥ᵢ` with `p₁(Bᵢ) ≠ p₂(Bᵢ)`; the example on p. 81
shows the proposition fails when only one player is informed of a subjective event. The
conclusion asks only for a pair of strategies (each `sᵢ` is `𝒥ᵢ`-measurable), **not** an
equilibrium point; each `Hᵢ` is computed under the player's own `pᵢ` (3.1), which is why
`H₁(s) + H₂(s)` may exceed `0`. The paper refers to this result as "Proposition 6.5" on p. 81
(misprint). -/
theorem zero_sum_both_exceed_value {Ω X : Type*} {mΩ : MeasurableSpace Ω}
    {S : Fin 2 → Type*} [∀ i, Fintype (S i)] [Fintype X]
    (R : RandomizingStructure (Fin 2) Ω mΩ) (hII : AssumptionII R)
    (g : (∀ i, S i) → X) (hg : Function.Surjective g) (u : Fin 2 → X → ℝ)
    (hzs : IsZeroSum u) (v : ℝ) (hv : IsValue u g v)
    (h62 : ∃ x y : X, u 0 x > v ∧ v > u 0 y)
    (h63 : ∀ i, ∃ B : Set Ω, MeasurableSet[R.J i] B ∧ IsSubjective R B) :
    ∃ s : ∀ i, Ω → S i, (∀ i, IsStrategy R i (s i)) ∧
      H R u g s 0 > v ∧ H R u g s 1 > -v := by sorry

end Aumann1974.ZeroSum
