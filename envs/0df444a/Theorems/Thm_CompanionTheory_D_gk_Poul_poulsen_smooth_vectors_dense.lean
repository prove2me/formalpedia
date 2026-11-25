-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_Poul_poulsen_smooth_vectors_dense
-- name    : CompanionTheory.D.gk.Poul.poulsen_smooth_vectors_dense
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:25:13.835685+00:00
-- url     : https://prove2.me/theorems/a1f2ba37-a987-5e17-912a-192b7fd47b77
-- title:
--   Poul: poulsen smooth vectors dense
-- statement:
--   The Poul construction uses the poulsen smooth vectors dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/HaarBumpFunctions/PoulsenSmoothVectorsDense.lean#L104-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/HaarBumpFunctions/PoulsenSmoothVectorsDense.lean#L104-L116

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

theorem CompanionTheory.D.gk.Poul.poulsen_smooth_vectors_dense : BranchingSupport.Poulsen := by sorry
