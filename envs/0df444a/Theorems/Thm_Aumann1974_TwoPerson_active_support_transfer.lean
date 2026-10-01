-- Prove2me | Theorems.Thm_Aumann1974_TwoPerson_active_support_transfer
-- name    : Aumann1974.TwoPerson.active_support_transfer
-- status  : Open
-- author  : @junyihjy
-- created : 2026-10-01T00:39:04.649523+00:00
-- url     : https://prove2.me/theorems/460e5ad8-afdf-4d51-9cab-92cf41edbefe
-- title:
--   Active-support transfer for mimicking objective strategies (Aumann 1974, Prop 5.1, null events (5.2) + mimicry ⇒ same active support)
-- statement:
--   Let R be a randomizing structure for a two-person game with finite pure strategy sets S 0, S 1, satisfying Aumann's common-null-events hypothesis (5.2): for every mΩ-measurable event B, p_0(B) = 0 iff p_1(B) = 0. Let s_1 be player 1's subjective mixed strategy and t_1 an objective mixed strategy that mimics it from player 2's viewpoint, p_2{t_1 = a_1} = p_2{s_1 = a_1} for every pure a_1 (the paper's (5.3)). Then for every pure strategy a, a is used with positive p_0-probability under s_1 iff it is used with positive p_0-probability under t_1: the mimicking objective strategy has exactly the same active support as the subjective one.
-- source:
--   Aumann 1974, Subjectivity and Correlation in Randomized Strategies, §5 (pp. 78–79), step 3 of the proof of Proposition 5.1 (null events (5.2) + mimicry (5.3) ⇒ same active support). Decomposition child B of Aumann1974.TwoPerson.two_person_mixed_equilibrium_objective (Prop 5.1); see ~/workspace/p2m_harness/aumann_subjective_triage.md §4.

import Mathlib
import Definitions.Def_Aumann1974_TwoPerson_RandomizingStructure
import Definitions.Def_Aumann1974_TwoPerson_Payoffs

namespace Aumann1974.TwoPerson

open MeasureTheory

/-- **Active-support transfer** (Aumann 1974, *Subjectivity and Correlation in
Randomized Strategies*, proof of Proposition 5.1, §5 pp. 78–79, step 3,
first half): under the common-null-events hypothesis (5.2) of the paper, an
objective mixed strategy `t₁` that mimics a subjective mixed strategy `s₁`
from player 2's viewpoint has exactly the same active support as `s₁`.

The paper's argument: (5.3) gives `p₂{t₁=a₁} = p₂{s₁=a₁}`; (5.2)
moves positivity `p₁↔p₂`; objectivity of `t₁` identifies `p₁` with
`p₂` on its events, so the strategies entering *actively* (positive
`p₁`-probability) into `s₁` are precisely those active in `t₁`.

**Formalization note.** Players are `0, 1 : Fin 2`. (5.2) is the hypothesis
`h52`, imposed for every `mΩ`-measurable event `B` exactly as in the parent
node `Aumann1974.TwoPerson.two_person_mixed_equilibrium_objective`. All
identifiers (`RandomizingStructure`, `AssumptionII`-free here, `R.p`,
`MeasurableSet[mΩ]`, `IsObjectiveStrategy`) are taken byte-identical from
the live mission records. -/
theorem active_support_transfer {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {S : Fin 2 → Type*} [∀ i, Fintype (S i)]
    (R : RandomizingStructure (Fin 2) Ω mΩ)
    (h52 : ∀ B : Set Ω, MeasurableSet[mΩ] B → (R.p 0 B = 0 ↔ R.p 1 B = 0))
    (s₁ t₁ : Ω → S 0)
    (hmimic : ∀ a : S 0, R.p 1 {ω | t₁ ω = a} = R.p 1 {ω | s₁ ω = a})
    (hobj : IsObjectiveStrategy R t₁) (a : S 0) :
    R.p 0 {ω | s₁ ω = a} = 0 ↔ R.p 0 {ω | t₁ ω = a} = 0 := by sorry

end Aumann1974.TwoPerson
