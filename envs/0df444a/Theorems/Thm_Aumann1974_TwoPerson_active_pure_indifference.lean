-- Prove2me | Theorems.Thm_Aumann1974_TwoPerson_active_pure_indifference
-- name    : Aumann1974.TwoPerson.active_pure_indifference
-- status  : Open
-- author  : @junyihjy
-- created : 2026-10-01T00:37:55.694103+00:00
-- url     : https://prove2.me/theorems/2a6b4c82-7e3a-42f6-bebe-b6629b02c533
-- title:
--   In a mixed equilibrium, every pure strategy used with positive probability yields the equilibrium payoff
-- statement:
--   In a mixed subjective equilibrium s of a two-person game (Aumann 1974, Proposition 5.1 proof step 3, p. 79), every pure strategy a that player i uses with positive probability under i's own subjective probability yields player i's equilibrium payoff: the payoff H_i of the constant-a deviation equals H_i(s).

import Mathlib
import Definitions.Def_Aumann1974_TwoPerson_RandomizingStructure
import Definitions.Def_Aumann1974_TwoPerson_Payoffs

namespace Aumann1974.TwoPerson

/-- **Active pure indifference** (Aumann 1974, *Subjectivity and Correlation in Randomized
Strategies*, proof of Proposition 5.1, step 3, p. 79): in a mixed equilibrium `s`, every
pure strategy `a` that player `i` uses with positive probability yields the equilibrium
payoff for `i` — the constant-`a` deviation is a legal strategy deviation in `IsEquilibrium`
(payoff ≤), while the weighted average of the active atoms equals `H` (via Lemma 7.3
factorization), forcing equality on positive-weight atoms. -/
theorem active_pure_indifference {Ω X : Type*} {mΩ : MeasurableSpace Ω}
    {S : Fin 2 → Type*} [∀ i, Fintype (S i)] [Fintype X]
    (R : RandomizingStructure (Fin 2) Ω mΩ) (hII : AssumptionII R)
    (g : (∀ i, S i) → X) (u : Fin 2 → X → ℝ)
    (s : ∀ i, Ω → S i) (hs : IsEquilibrium R u g s) (hmix : ∀ i, IsMixed R i (s i))
    (i : Fin 2) (a : S i) (hpos : R.p i {ω | s i ω = a} ≠ 0) :
    H R u g (Function.update s i (fun _ => a)) i = H R u g s i := by sorry

end Aumann1974.TwoPerson
