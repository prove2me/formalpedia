-- Prove2me | Theorems.Thm_BanditAlgorithm_gittinsFiniteRetirementValue_mono_of_integrable
-- name    : BanditAlgorithm.gittinsFiniteRetirementValue_mono_of_integrable
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-31T04:48:25.071141+00:00
-- url     : https://prove2.me/theorems/05151385-1d56-44cc-b9ac-eface8aeaccb
-- title:
--   Finite-horizon Gittins retirement values are monotone in the horizon
-- statement:
--   Consider the finite-horizon value functions for a discounted one-armed retirement game. At horizon zero the value is zero, while at horizon $n+1$ the player chooses between retiring for zero and playing once for reward $r(x)-\gamma$ followed by the discounted continuation value at horizon $n$.
--
--   Assume $\alpha\ge 0$ and that every finite-horizon continuation value is integrable against every transition measure $P(x,\cdot)$. Then extending the available horizon cannot decrease the value:
--
--   $$
--   V_n^{\gamma}(x)\le V_{n+1}^{\gamma}(x)
--   \qquad\text{for every }n\ge0\text{ and state }x.
--   $$
--
--   This is the monotonicity input used to pass from finite-horizon dynamic programming to the infinite-horizon Wald--Bellman equation for the discounted retirement problem.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (Cambridge University Press, 2020), printed p. 442, Theorem 35.3 (finite-horizon approximation underlying the infinite-horizon Wald--Bellman equation), and printed p. 449, Lemma 35.7(a).

import Definitions.Def_GittinsFiniteRetirementValue

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.gittinsFiniteRetirementValue_mono_of_integrable
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) (r : S → ℝ) (α γ : ℝ) (hα0 : 0 ≤ α)
    (hint : ∀ n x, Integrable (gittinsFiniteRetirementValue P r α γ n) (P x)) :
    ∀ n x,
      gittinsFiniteRetirementValue P r α γ n x ≤
        gittinsFiniteRetirementValue P r α γ (n + 1) x := by
  sorry
