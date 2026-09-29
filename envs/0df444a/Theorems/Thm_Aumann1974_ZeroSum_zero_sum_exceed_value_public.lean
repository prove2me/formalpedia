-- Prove2me | Theorems.Thm_Aumann1974_ZeroSum_zero_sum_exceed_value_public
-- name    : Aumann1974.ZeroSum.zero_sum_exceed_value_public
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:07:33.626689+00:00
-- url     : https://prove2.me/theorems/74efe4ce-6ebd-4f68-b543-141aa98fff8c
-- title:
--   Remark after Proposition 6.1 — with a public subjective event and a public roulette, both zero-sum players can beat the value
-- statement:
--   Let $G$ be a two-person zero-sum game: finite pure strategy sets $S_1,S_2$, a finite outcome set $X$, an outcome function $g:S_1\times S_2\to X$ onto $X$, and utilities with $u_1(x)+u_2(x)=0$ for all $x$. Let $v$ be its **value** (player 1's payoff at a Nash equilibrium of the mixed extension). Let $(\Omega,\mathcal B,\mathcal J_1,\mathcal J_2,p_1,p_2)$ be a randomizing structure satisfying Assumption II. Assume
--
--   1. (6.2) there are outcomes $x,y\in X$ with $u_1(x) > v > u_1(y)$;
--   2. (6.5) there is a public subjective event $B$ ($B\in\mathcal J_1\cap\mathcal J_2$ with $p_1(B)\ne p_2(B)$), and there is a public roulette.
--
--   Then there is a pair $s=(s_1,s_2)$ of strategies ($s_i$ measurable with respect to $\mathcal J_i$) such that
--   $$H_1(s) > v,\qquad H_2(s) > -v,$$
--   where $H_i(s)=\int_\Omega u_i(g(s(\omega)))\,dp_i(\omega)$ is computed under player $i$'s own subjective probability.
--
--   The paper states this as the easy special case of Proposition 6.1 in which the players share a subjective event and a correlating device: both can agree on a bet whose outcome each rates in his own favour, so that each expects more than the value.
--
--   **Formalization Note** The pair $s$ is not required to be an equilibrium point: the paper's point is a binding agreement. The value is pinned through `AGT.IsMixedNash`; by the minimax theorem it is unique.
-- source:
--   R. J. Aumann, Subjectivity and Correlation in Randomized Strategies, J. Math. Econ. 1 (1974) 67–96, https://doi.org/10.1016/0304-4068(74)90037-8, Sect. 6, p. 80 (PDF p. 14), Remark following Proposition 6.1, condition (6.5); value defined p. 79 (PDF p. 13)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_Aumann1974_ZeroSum_RandomizingStructure
import Definitions.Def_Aumann1974_ZeroSum_Payoffs

namespace Aumann1974.ZeroSum

open MeasureTheory

/-- **Remark following Proposition 6.1** (Aumann 1974, *Subjectivity and Correlation in
Randomized Strategies*, J. Math. Econ. 1, Sect. 6, p. 80, PDF p. 14): "The proposition is
considerably easier to prove if one assumes that (6.5) there is a public subjective event `B` and
there is a public roulette." — and, at the end of the Remark, "the proposition is proved under
the assumption of (6.5)". Stated: let `G` be a 2-person 0-sum game with value `v`; assume (6.2)
there are outcomes `x` and `y` with `u₁(x) > v > u₁(y)`, and (6.5). Then there is a pair `s` of
strategies such that (6.4) `H₁(s) > v`, `H₂(s) > −v`.

**Formalization Note.** Players `1, 2` are `0, 1 : Fin 2`; `S 0`, `S 1` and `X` are finite, `g`
is onto `X` and `u` is the adopted zero-sum pair of utilities (`IsZeroSum`). `v` is **the value**
(`IsValue`: player 1's payoff at a Nash equilibrium of the mixed extension, which by the minimax
theorem is unique), not a free real. Assumption II (standing assumption, p. 75) is a hypothesis.
(6.5) replaces (6.3) of Proposition 6.1: a public event `B` (in `𝒥₁ ∩ 𝒥₂`) with
`p₁(B) ≠ p₂(B)`, and a public roulette. The conclusion asks only for a pair of strategies (each
`sᵢ` is `𝒥ᵢ`-measurable), **not** an equilibrium point; each `Hᵢ` is computed under the player's
own `pᵢ`. -/
theorem zero_sum_exceed_value_public {Ω X : Type*} {mΩ : MeasurableSpace Ω}
    {S : Fin 2 → Type*} [∀ i, Fintype (S i)] [Fintype X]
    (R : RandomizingStructure (Fin 2) Ω mΩ) (hII : AssumptionII R)
    (g : (∀ i, S i) → X) (hg : Function.Surjective g) (u : Fin 2 → X → ℝ)
    (hzs : IsZeroSum u) (v : ℝ) (hv : IsValue u g v)
    (h62 : ∃ x y : X, u 0 x > v ∧ v > u 0 y)
    (h65 : (∃ B : Set Ω, IsPublic R B ∧ IsSubjective R B) ∧
      ∃ m : MeasurableSpace Ω, IsPublicRoulette R m) :
    ∃ s : ∀ i, Ω → S i, (∀ i, IsStrategy R i (s i)) ∧
      H R u g s 0 > v ∧ H R u g s 1 > -v := by sorry

end Aumann1974.ZeroSum
