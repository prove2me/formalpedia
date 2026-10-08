-- Prove2me | Theorems.Thm_Aumann1974_TwoPerson_mimic_payoff_transfer
-- name    : Aumann1974.TwoPerson.mimic_payoff_transfer
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-01T01:48:30.437603+00:00
-- url     : https://prove2.me/theorems/e25e92e4-c438-4df5-8118-18082bd347d7
-- title:
--   Mimic payoff transfer: an objective mimicking strategy keeps player 1's equilibrium payoff (Aumann 1974, Prop 5.1, (5.6))
-- statement:
--   In a two-person game with finite pure strategy sets S 0, S 1 satisfying Aumann's common-null-events hypothesis (5.2) (p_0(B) = 0 iff p_1(B) = 0 for every measurable event B), let s be a mixed subjective equilibrium and let t_1 be an objective mixed strategy that mimics player 1's subjective strategy from player 2's viewpoint: p_2{t_1 = a_1} = p_2{s_1 = a_1} for every pure a_1 (the paper's (5.3)). Then replacing s_1 by t_1 leaves player 1's payoff unchanged: H_1(t_1, s_2) = H_1(s_1, s_2) (the paper's equation (5.6), Aumann 1974, proof of Proposition 5.1, p. 79).
-- source:
--   Aumann 1974, Subjectivity and Correlation in Randomized Strategies, §5 (pp. 78–79), step 3 of the proof of Proposition 5.1 (mimicry + indifference on the active support ⇒ payoff identity (5.6)). Decomposition child C of Aumann1974.TwoPerson.two_person_mixed_equilibrium_objective (Prop 5.1); depends on proved Lemma 7.3 (cbc18ddc, prob_profile_factor) plus sibling children active_support_transfer and active_pure_indifference; see ~/workspace/p2m_harness/aumann_subjective_triage.md §4.

import Mathlib
import Definitions.Def_Aumann1974_TwoPerson_RandomizingStructure
import Definitions.Def_Aumann1974_TwoPerson_Payoffs

namespace Aumann1974.TwoPerson

open MeasureTheory

/-- **Mimic payoff transfer** (Aumann 1974, *Subjectivity and Correlation in Randomized
Strategies*, proof of Proposition 5.1, step 3, second half, p. 79): mimicry plus
indifference on the active support implies that replacing player 1's subjective
strategy `s₁` by the objective mimicking strategy `t₁` leaves player 1's payoff
unchanged, `H₁(t₁, s₂) = H₁(s₁, s₂)` (the paper's (5.6)).

The paper's argument: the profile's probability factorizes by Lemma 7.3
(`prob_profile_factor`, mission node `cbc18ddc`, proved); the mimicking
objective strategy `t₁` has exactly the active support of `s₁` under the
common-null-events hypothesis (5.2) (the sibling node `active_support_transfer`);
and every positively-weighted pure atom pays the equilibrium payoff (the
sibling node `active_pure_indifference`). The weighted sum over `t₁`'s
support therefore hits the equilibrium payoff on every active atom, giving
(5.6). Players are `0, 1 : Fin 2`; `IsEquilibrium` is used only as an opaque
hypothesis (deviation encoding as in the parent node). -/
theorem mimic_payoff_transfer {Ω X : Type*} {mΩ : MeasurableSpace Ω}
    {S : Fin 2 → Type*} [∀ i, Fintype (S i)] [Fintype X]
    (R : RandomizingStructure (Fin 2) Ω mΩ) (hII : AssumptionII R)
    (g : (∀ i, S i) → X) (u : Fin 2 → X → ℝ)
    (h52 : ∀ B : Set Ω, MeasurableSet[mΩ] B → (R.p 0 B = 0 ↔ R.p 1 B = 0))
    (s : ∀ i, Ω → S i) (hs : IsEquilibrium R u g s) (hmix : ∀ i, IsMixed R i (s i))
    (t₁ : Ω → S 0) (hobj : IsObjectiveStrategy R t₁) (hmix₁ : IsMixed R 0 t₁)
    (hmimic : ∀ a : S 0, R.p 1 {ω | t₁ ω = a} = R.p 1 {ω | s 0 ω = a}) :
    H R u g (fun i => if h : i = 0 then h ▸ t₁ else s i) 0 = H R u g s 0 := by sorry

end Aumann1974.TwoPerson
