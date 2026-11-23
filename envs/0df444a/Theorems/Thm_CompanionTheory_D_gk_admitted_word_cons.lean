-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
-- name    : CompanionTheory.D.gk.admitted.word_cons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:02:33.440127+00:00
-- url     : https://prove2.me/theorems/8ee032c8-95bd-4e72-a00e-ba28c0156622
-- title:
--   admitted: word cons
-- statement:
--   The admitted construction uses the word cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/MapStdPoly.lean#L20-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/MapStdPoly.lean#L20-L20

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

theorem CompanionTheory.D.gk.admitted.word_cons (E a : R) (l : List R) : word E (a :: l) = E * a * word E l := by sorry

attribute [defeq] CompanionTheory.D.gk.admitted.word_cons
