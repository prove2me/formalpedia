-- Prove2me | Theorems.Thm_Aumann1974_TwoPerson_nash_payoffs_eq_objective_mixed
-- name    : Aumann1974.TwoPerson.nash_payoffs_eq_objective_mixed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T10:52:37.437967+00:00
-- url     : https://prove2.me/theorems/a94e066b-e831-463f-a096-424db0d98724
-- title:
--   Proposition 4.3 — Nash equilibrium payoffs = objective mixed equilibrium payoffs
-- statement:
--   Consider a game with a finite set $N$ of players, finite pure strategy sets $S_i$, a finite outcome set $X$, an outcome function $g : S \to X$ onto $X$, and utilities $u_i : X\to\mathbb R$; write $h_i = u_i\circ g$. Let $(\Omega,\mathcal B,(\mathcal J_i),(p_i))$ be a randomizing structure satisfying Assumption II.
--
--   For an $n$-tuple $\sigma = (\sigma_1,\dots,\sigma_n)$ of distributions on $S_1,\dots,S_n$ put
--   $$F_i(\sigma) = \sum_{a\in S} h_i(a)\prod_{j\in N}\sigma_j(a_j).$$
--   $\sigma$ is a **Nash equilibrium point** if $F_i(\sigma) \ge F_i(\sigma_1,\dots,\sigma_{i-1},\tau_i,\sigma_{i+1},\dots,\sigma_n)$ for every $i$ and every distribution $\tau_i$ on $S_i$; then $F(\sigma)$ is a *Nash equilibrium payoff*. An *objective mixed equilibrium payoff* is $H(s)$ for an equilibrium point $s$ (no player gains by deviating to **any** strategy) all of whose strategies are objective and mixed. Then
--   $$\{F(\sigma) : \sigma \text{ a Nash equilibrium point}\} = \{H(s) : s \text{ an equilibrium point in objective mixed strategies}\}$$
--   as sets of payoff vectors in $\mathbb R^N$.
--
--   The proposition says that the classical theory of mixed-strategy equilibrium is exactly the objective, mixed part of Aumann's model. Together with Nash's theorem it gives the existence of an equilibrium point in every game.
--
--   **Formalization Note** Distributions, $F_i$ and Nash equilibrium points are `AGT.IsLottery`, `AGT.expectedPayoff` and `AGT.IsMixedNash` from the definition `agt_games`, applied to the payoff $h_i(a) = u_i(g(a))$. $H(s)$ is the vector $i\mapsto H_i(s)$, each coordinate computed under player $i$'s own $p_i$.
-- source:
--   R. J. Aumann, Subjectivity and Correlation in Randomized Strategies, J. Math. Econ. 1 (1974) 67–96, https://doi.org/10.1016/0304-4068(74)90037-8, p. 77 (PDF p. 11), Proposition 4.3; F_i and Nash equilibrium point p. 77; proof pp. 83–84 (PDF pp. 17–18)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_Aumann1974_TwoPerson_RandomizingStructure
import Definitions.Def_Aumann1974_TwoPerson_Payoffs

namespace Aumann1974.TwoPerson

open MeasureTheory

/-- **Proposition 4.3** (Aumann 1974, *Subjectivity and Correlation in Randomized Strategies*,
J. Math. Econ. 1, p. 77, PDF p. 11; proof pp. 83–84): the set of Nash equilibrium payoffs
coincides with the set of objective mixed equilibrium payoffs.

The game: finite players `ι`, finite pure strategy sets `Sᵢ`, finite outcomes `X`, an outcome
function `g : S → X` onto `X`, utilities `uᵢ : X → ℝ`, pure payoffs `hᵢ = uᵢ ∘ g`, on a
randomizing structure `R` satisfying Assumption II.

* A **Nash equilibrium payoff** is `F(σ) = (F₁(σ), …, Fₙ(σ))`, `Fᵢ(σ) = ∑ₐ hᵢ(a) ∏ⱼ σⱼ(aⱼ)`, for a
  Nash equilibrium point `σ` (an `n`-tuple of distributions from which no player gains by
  switching to another distribution `τᵢ`), p. 77: `AGT.IsMixedNash` and `AGT.expectedPayoff`.
* An **objective mixed equilibrium payoff** is `H(s)` for an equilibrium point `s` (deviations over
  all strategies) whose strategies `sᵢ` are all objective and mixed, p. 76.

**Formalization Note.** Payoff vectors live in `ι → ℝ`; `H(s)` is `fun i => H R u g s i`, each
coordinate computed under that player's own `pᵢ`. -/
theorem nash_payoffs_eq_objective_mixed {ι Ω X : Type*} [Fintype ι] [DecidableEq ι]
    {mΩ : MeasurableSpace Ω} {S : ι → Type*} [∀ i, Fintype (S i)] [Fintype X]
    (R : RandomizingStructure ι Ω mΩ) (hII : AssumptionII R)
    (g : (∀ i, S i) → X) (hg : Function.Surjective g) (u : ι → X → ℝ) :
    {v : ι → ℝ | ∃ σ : ∀ i, S i → ℝ, AGT.IsMixedNash (payoffFn u g) σ ∧
        v = fun i => AGT.expectedPayoff (payoffFn u g) σ i} =
      {v : ι → ℝ | ∃ s : ∀ i, Ω → S i, IsEquilibrium R u g s ∧
        (∀ i, IsObjectiveStrategy R (s i) ∧ IsMixed R i (s i)) ∧
        v = fun i => H R u g s i} := by sorry

end Aumann1974.TwoPerson
