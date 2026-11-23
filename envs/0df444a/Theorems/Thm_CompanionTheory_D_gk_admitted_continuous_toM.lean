-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_continuous_toM
-- name    : CompanionTheory.D.gk.admitted.continuous_toM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:00.35511+00:00
-- url     : https://prove2.me/theorems/761bc5b7-4a3e-427c-aaa6-a23a276d3600
-- title:
--   admitted: continuous to M
-- statement:
--   The admitted construction uses the continuous to M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/AdmissibleOfFiniteRank.lean#L32-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/AdmissibleOfFiniteRank.lean#L32-L32

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_InPCommutatorOfInK
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_AdmissibleOfFiniteRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open PI.UpqRep
variable {n : ℕ} {ε : Fin n → Bool}

theorem CompanionTheory.D.gk.admitted.continuous_toM : Continuous (toM : UJ ε → Matrix (Fin n) (Fin n) ℂ) := by sorry
