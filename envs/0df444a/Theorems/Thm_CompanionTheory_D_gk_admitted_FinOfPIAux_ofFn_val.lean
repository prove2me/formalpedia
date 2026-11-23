-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_ofFn_val
-- name    : CompanionTheory.D.gk.admitted.FinOfPIAux.ofFn_val
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:30:00.440855+00:00
-- url     : https://prove2.me/theorems/3ea6ec5d-6e1a-4d5e-a2c3-9025dcfc86db
-- title:
--   Fin Of PIAux: of Fn val
-- statement:
--   The Fin Of PIAux construction uses the of Fn val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/FinOfPI.lean#L238-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/FinOfPI.lean#L238-L239

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
variable (E : H →L[ℂ] H) (M : ℕ) (φ : ℕ → H →L[ℂ] ℂ) (x : ℕ → H)

theorem CompanionTheory.D.gk.admitted.FinOfPIAux.ofFn_val (M : ℕ) : (List.ofFn fun i : Fin M => (i : ℕ)) = List.range' 0 M := by sorry
