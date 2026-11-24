-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_Poul_vanish_or_equiv
-- name    : CompanionTheory.D.gk.Poul.vanish_or_equiv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:37:30.771942+00:00
-- url     : https://prove2.me/theorems/f84f61a4-3f09-4403-91c6-d244e6c9f333
-- title:
--   Poul: vanish or equiv
-- statement:
--   The Poul construction uses the vanish or equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/HaarBumpFunctions/PoulsenSmoothVectorsDense.lean#L85-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/HaarBumpFunctions/PoulsenSmoothVectorsDense.lean#L85-L102

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_Unimod
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeries__Poulsen_b54a5a55a6942064
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_PoulsenSmoothVectorsDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.Poul
open PI PI.UpqRep CompanionTheory.D.Upq.ModEx CompanionTheory.D.Upq.Sm CompanionTheory.D.gk.admitted CompanionTheory.LimBd
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem CompanionTheory.D.gk.Poul.vanish_or_equiv {ε ε' : Fin (2 * r + k + 1) → Bool} {mu mu' : Fin (2 * r + k + 1) → ℝ} {R R' : BranchingSupport.Rep k r}
    (hR : R.IsDS ε mu) (hR' : R'.IsDS ε' mu') {B : R.H → R'.H → ℂ} (hB : BranchingSupport.IsInvForm R R' B) :
    (∀ x ∈ R.sm, ∀ y ∈ R'.sm, B x y = 0) ∨
      ∃ U : R.H ≃ₗᵢ[ℂ] R'.H, ∀ g ∈ BranchingSupport.GG k r, ∀ x, U (R.σ g x) = R'.σ g (U x) := by sorry
