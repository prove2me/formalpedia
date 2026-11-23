-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_map_stdPoly
-- name    : CompanionTheory.D.gk.admitted.map_stdPoly
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:31:35.104465+00:00
-- url     : https://prove2.me/theorems/d1a2d110-26a0-46f9-9e88-386ce927f117
-- title:
--   admitted: map std Poly
-- statement:
--   The admitted construction uses the map std Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/MapStdPoly.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/MapStdPoly.lean#L31-L33

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

theorem CompanionTheory.D.gk.admitted.map_stdPoly {R' : Type*} [Ring R'] (f : R →+* R') (E : R) {M : ℕ} (a : Fin M → R) :
    f (stdPoly E a) = stdPoly (f E) fun i => f (a i) := by sorry
