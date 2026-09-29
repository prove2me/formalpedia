-- Prove2me | Theorems.Thm_Aumann1974_TwoPerson_two_person_mixed_equilibrium_objective
-- name    : Aumann1974.TwoPerson.two_person_mixed_equilibrium_objective
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T10:57:05.695357+00:00
-- url     : https://prove2.me/theorems/a2e36b73-bf42-4394-a441-ee96d30ca67a
-- title:
--   Proposition 5.1 — in a two-person game, every mixed subjective equilibrium payoff is an objective mixed equilibrium payoff
-- statement:
--   Let $G$ be a two-person game (not necessarily zero-sum): players $1,2$ with finite pure strategy sets $S_1,S_2$, a finite outcome set $X$, an outcome function $g : S_1\times S_2 \to X$ onto $X$, and utilities $u_1,u_2 : X\to\mathbb R$. Let $(\Omega,\mathcal B,(\mathcal J_1,\mathcal J_2),(p_1,p_2))$ be a randomizing structure satisfying Assumption II, and assume that the two subjective probabilities have the same null events:
--   $$\text{(5.2)}\qquad p_1(B) = 0 \iff p_2(B) = 0\qquad\text{for every event } B\in\mathcal B.$$
--   Then for every equilibrium point $s = (s_1,s_2)$ in **mixed** strategies there is an equilibrium point $t=(t_1,t_2)$ in **objective mixed** strategies with the same payoff vector:
--   $$H(s) = H(t),\qquad\text{i.e.}\quad H_1(s)=H_1(t)\ \text{and}\ H_2(s)=H_2(t).$$
--
--   Aumann's Example 2.3 shows that with three players, pegging strategies on subjective events can yield a mixed equilibrium better for every player than any objective mixed equilibrium. This proposition shows that with two players it cannot: subjectivity alone, without correlation, adds no new equilibrium payoffs. Example 2.9 shows the hypothesis "mixed" cannot be dropped.
--
--   **Formalization Note** The players $1,2$ are `0, 1 : Fin 2`. Equilibrium points allow deviations to **any** strategy measurable with respect to the deviator's information. (5.2) is imposed on all $\mathcal B$-measurable events. Each coordinate of $H$ is computed under that player's own subjective probability.
-- source:
--   R. J. Aumann, Subjectivity and Correlation in Randomized Strategies, J. Math. Econ. 1 (1974) 67–96, https://doi.org/10.1016/0304-4068(74)90037-8, p. 78 (PDF p. 12), Proposition 5.1 with condition (5.2) and footnote 16; proof p. 79 (PDF p. 13)

import Mathlib
import Definitions.Def_Aumann1974_TwoPerson_RandomizingStructure
import Definitions.Def_Aumann1974_TwoPerson_Payoffs

namespace Aumann1974.TwoPerson

open MeasureTheory

/-- **Proposition 5.1** (Aumann 1974, *Subjectivity and Correlation in Randomized Strategies*,
J. Math. Econ. 1, p. 78, PDF p. 12): let `G` be a 2-person game (not necessarily 0-sum,
footnote 16), and assume that
(5.2) for any event `B`, `p₁(B) = 0` if and only if `p₂(B) = 0`.
Then for each equilibrium point `s` in mixed strategies, there is an equilibrium point `t` in
objective mixed strategies such that `H(s) = H(t)`.

**Formalization Note.** The two players `1, 2` are `0, 1 : Fin 2`. The game has finite pure
strategy sets `S 0`, `S 1`, a finite outcome set `X`, an outcome function `g` onto `X` and
utilities `u`; the randomizing structure `R` satisfies Assumption II (standing assumption,
p. 75). (5.2) is imposed for every `ℬ`-measurable `B` (the paper's events). An equilibrium point
(`IsEquilibrium`) is a profile of strategies against which no player gains by deviating to
**any** strategy. `s` is assumed mixed for both players; the conclusion requires `t` to be both
objective and mixed for both players. `H(s) = H(t)` is equality of payoff vectors: each player's
payoff is computed under that player's own `pᵢ`. -/
theorem two_person_mixed_equilibrium_objective {Ω X : Type*} {mΩ : MeasurableSpace Ω}
    {S : Fin 2 → Type*} [∀ i, Fintype (S i)] [Fintype X]
    (R : RandomizingStructure (Fin 2) Ω mΩ) (hII : AssumptionII R)
    (g : (∀ i, S i) → X) (hg : Function.Surjective g) (u : Fin 2 → X → ℝ)
    (h52 : ∀ B : Set Ω, MeasurableSet[mΩ] B → (R.p 0 B = 0 ↔ R.p 1 B = 0))
    (s : ∀ i, Ω → S i) (hs : IsEquilibrium R u g s) (hmix : ∀ i, IsMixed R i (s i)) :
    ∃ t : ∀ i, Ω → S i, IsEquilibrium R u g t ∧
      (∀ i, IsObjectiveStrategy R (t i) ∧ IsMixed R i (t i)) ∧
      (fun i => H R u g s i) = fun i => H R u g t i := by sorry

end Aumann1974.TwoPerson
