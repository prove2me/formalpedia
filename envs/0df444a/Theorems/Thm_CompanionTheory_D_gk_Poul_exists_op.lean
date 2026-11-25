-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_Poul_exists_op
-- name    : CompanionTheory.D.gk.Poul.exists_op
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:55:36.280274+00:00
-- url     : https://prove2.me/theorems/e8f7c230-fb13-5d0a-ad97-e8f0660a5b4b
-- title:
--   Poul: exists op
-- statement:
--   The Poul construction uses the exists op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/HaarBumpFunctions/PoulsenSmoothVectorsDense.lean#L56-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/HaarBumpFunctions/PoulsenSmoothVectorsDense.lean#L56-L83

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_Unimod
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeries__Poulsen_b54a5a55a6942064
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_PoulsenSmoothVectorsDense
import Theorems.Thm_CompanionTheory_D_gk_Poul_IsInv_exists_op

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

theorem CompanionTheory.D.gk.Poul.exists_op {ε ε' : Fin (2 * r + k + 1) → Bool} {mu mu' : Fin (2 * r + k + 1) → ℝ} {R R' : BranchingSupport.Rep k r}
    (hR : R.IsDS ε mu) (hR' : R'.IsDS ε' mu') {B : R.H → R'.H → ℂ} (hB : BranchingSupport.IsInvForm R R' B) :
    ∃ T : R'.H →L[ℂ] R.H, (∀ g ∈ UH (Hpk k r), ∀ y, T (R'.σ g y) = R.σ g (T y)) ∧
      ∀ x ∈ R.sm, ∀ y ∈ R'.sm, B x y = ⟪T y, x⟫_ℂ := by sorry
