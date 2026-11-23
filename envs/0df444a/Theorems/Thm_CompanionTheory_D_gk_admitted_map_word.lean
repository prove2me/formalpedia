-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_map_word
-- name    : CompanionTheory.D.gk.admitted.map_word
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:31:28.048476+00:00
-- url     : https://prove2.me/theorems/93e925d9-1475-4b0c-99fe-e163c54ab445
-- title:
--   admitted: map word
-- statement:
--   The admitted construction uses the map word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/MapStdPoly.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/MapStdPoly.lean#L25-L29

import Definitions.Def_Formalism_PeriodIntegrals_KFinSmooth
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open PI.UpqRep
variable {R : Type*} [Ring R]

theorem CompanionTheory.D.gk.admitted.map_word {R' : Type*} [Ring R'] (f : R →+* R') (E : R) (l : List R) :
    f (word E l) = word (f E) (l.map f) := by sorry
