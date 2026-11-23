-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_unitary_group_admissible
-- name    : CompanionTheory.D.gk.admitted.unitary_group_admissible
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:51:58.602836+00:00
-- url     : https://prove2.me/theorems/ef285656-56f5-47c3-89c7-ca189cbdffd3
-- title:
--   admitted: unitary group admissible
-- statement:
--   The admitted construction uses the unitary group admissible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/FinalAll.lean#L10-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/FinalAll.lean#L10-L10

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_AdmissibleOfIwasawa
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaAll
import Definitions.Def_Formalism_PeriodIntegrals_PhMeasCore
import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinalAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open PI.UpqRep

theorem CompanionTheory.D.gk.admitted.unitary_group_admissible (n : ℕ) (ε : Fin n → Bool) : AdmUJ ε := by sorry
