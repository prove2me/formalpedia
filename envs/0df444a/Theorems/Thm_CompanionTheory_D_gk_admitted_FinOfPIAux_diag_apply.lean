-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_diag_apply
-- name    : CompanionTheory.D.gk.admitted.FinOfPIAux.diag_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:18.521938+00:00
-- url     : https://prove2.me/theorems/74366875-5f78-49d4-914f-146a7c53a8b4
-- title:
--   Fin Of PIAux: diag apply
-- statement:
--   The Fin Of PIAux construction uses the diag apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/FinOfPI.lean#L54-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/FinOfPI.lean#L54-L54

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinOfPI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open CompanionTheory.D.gk.admitted.FinOfPIAux
variable {G : Type} [Group G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [CompleteSpace H] [Fintype ι] [DecidableEq ι]

theorem CompanionTheory.D.gk.admitted.FinOfPIAux.diag_apply (T : H →L[ℂ] H) (z : PiLp 2 (fun _ : ι => H)) (i : ι) : diag T z i = T (z i) := by sorry

attribute [defeq] CompanionTheory.D.gk.admitted.FinOfPIAux.diag_apply
