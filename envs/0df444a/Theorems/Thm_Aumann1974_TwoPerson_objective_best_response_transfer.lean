-- Prove2me | Theorems.Thm_Aumann1974_TwoPerson_objective_best_response_transfer
-- name    : Aumann1974.TwoPerson.objective_best_response_transfer
-- status  : Disproved
-- author  : @junyihjy
-- created : 2026-10-01T01:43:05.97083+00:00
-- url     : https://prove2.me/theorems/e29c7205-7ffa-4650-aacb-5a984846efcc
-- title:
--   Best-response transfer: the mimicking objective profile is an objective mixed equilibrium (Aumann 1974, Prop 5.1, step 4)
-- statement:
--   Let R be a randomizing structure for a two-person game with finite pure strategy sets S 0, S 1, satisfying Aumann's Assumption II. Let s be a subjective mixed equilibrium profile and t an objective mixed strategy profile for both players (each t i is objective and mixed) with the same payoff vector as s (the step-3 payoff identity (5.6), via mimicry (5.3)/(5.4): H_i(t) = H_i(s) for both players). If no player can strictly improve t by a unilateral deviation (H R u g t i ≤ H R u g (Function.update t i σ) i for every player i and deviation σ), then t is itself an objective mixed equilibrium with the same payoff vector as s: IsEquilibrium R u g t ∧ (fun i => H R u g s i) = fun i => H R u g t i.
-- source:
--   Aumann 1974, Subjectivity and Correlation in Randomized Strategies, §5 (pp. 78–79), step 4 of the proof of Proposition 5.1 (payoff identity + mimicry ⇒ (t1,t2) objective mixed equilibrium). Decomposition child D of Aumann1974.TwoPerson.two_person_mixed_equilibrium_objective (Prop 5.1); see ~/workspace/p2m_harness/aumann_subjective_triage.md §4.

import Mathlib
import Definitions.Def_Aumann1974_TwoPerson_RandomizingStructure
import Definitions.Def_Aumann1974_TwoPerson_Payoffs

namespace Aumann1974.TwoPerson

/-- **Objective best-response transfer** (Aumann 1974, *Subjectivity and Correlation in
Randomized Strategies*, proof of Proposition 5.1, step 4, p. 79): if the mimicking
objective profile `t` (objective and mixed for both players) yields the same payoff
vector as the subjective equilibrium profile `s` — the paper's step-3 payoff identity
(5.6), applied symmetrically via the (5.4) indistinguishability — and no player can
strictly improve on `t` by a unilateral deviation, then `t` is itself an objective
mixed equilibrium with the same payoff vector as `s`.

The paper's argument: `s` in equilibrium ⇒ optimality given `s` transfers to
optimality given `t` because player 1's payoff depends only on the distribution he
ascribes (mimicry (5.3)/(5.4) makes `t` indistinguishable from `s` from each player's
viewpoint); the symmetric argument covers player 2; the per-player optimality
assembles into `IsEquilibrium`.

**Formalization note.** Players are `0, 1 : Fin 2`. `IsEquilibrium` is used only as
an opaque hypothesis/conclusion, with identifier argument order `R u g <profile>`
verbatim from the live mission record of
`Aumann1974.TwoPerson.two_person_mixed_equilibrium_objective`; `H R u g <profile> i`
is likewise byte-identical to that record. All other identifiers
(`RandomizingStructure`, `AssumptionII`, `IsObjectiveStrategy`, `IsMixed`,
`Function.update`) are taken byte-identical from the live mission records. The
best-response hypothesis is stated inline as the no-profitable-deviation inequality
rather than via any named predicate. -/
theorem objective_best_response_transfer {Ω X : Type*} {mΩ : MeasurableSpace Ω}
    {S : Fin 2 → Type*} [∀ i, Fintype (S i)] [Fintype X]
    (R : RandomizingStructure (Fin 2) Ω mΩ) (hII : AssumptionII R)
    (g : (∀ i, S i) → X) (u : Fin 2 → X → ℝ)
    (s t : ∀ i, Ω → S i)
    (hobj : ∀ i, IsObjectiveStrategy R (t i)) (hmix : ∀ i, IsMixed R i (t i))
    (heq : (fun i => H R u g s i) = fun i => H R u g t i)
    (hbr : ∀ i, ∀ σ : Ω → S i, H R u g t i ≤ H R u g (Function.update t i σ) i) :
    IsEquilibrium R u g t ∧ (fun i => H R u g s i) = fun i => H R u g t i := by sorry

end Aumann1974.TwoPerson
