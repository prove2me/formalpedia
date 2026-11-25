-- Prove2me | Theorems.Thm_CompanionTheory_Bmu_spanFam
-- name    : CompanionTheory.Bmu.spanFam
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:15:28.237062+00:00
-- url     : https://prove2.me/theorems/9b000083-a8cc-4a65-a6f9-56f8c6f51ab0
-- title:
--   Bmu: span Fam
-- statement:
--   The Bmu construction uses the span Fam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselOrbitBounds/BesselMapUniqueness/NormPsiGen.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselOrbitBounds/BesselMapUniqueness/NormPsiGen.lean#L13-L20

import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_NormPsiGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm
open scoped ContDiff InnerProductSpace ComplexConjugate
noncomputable section
open CompanionTheory CompanionTheory.Bmu
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem CompanionTheory.Bmu.spanFam {n : ℕ} (S : Submodule ℝ (Mat n)) : ∃ (d : ℕ) (X : Fin d → Mat n), (∀ j, X j ∈ S) ∧
    ∀ Y ∈ S, ∃ a : Fin d → ℝ, Y = ∑ j, (a j : ℂ) • X j := by sorry
