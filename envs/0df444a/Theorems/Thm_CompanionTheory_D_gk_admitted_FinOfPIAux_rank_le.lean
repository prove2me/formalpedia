-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_rank_le
-- name    : CompanionTheory.D.gk.admitted.FinOfPIAux.rank_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:30:19.591121+00:00
-- url     : https://prove2.me/theorems/fbcd4823-907f-411a-adf6-97f50f32b715
-- title:
--   Fin Of PIAux: rank le
-- statement:
--   The Fin Of PIAux construction uses the rank le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/FinOfPI.lean#L284-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/FinOfPI.lean#L284-L305

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
omit [CompleteSpace H]

theorem CompanionTheory.D.gk.admitted.FinOfPIAux.rank_le (E : H →L[ℂ] H) (M : ℕ) (h : ∀ a : Fin M → H →L[ℂ] H, stdPoly E a = 0) :
    Module.rank ℂ (LinearMap.range (E : H →ₗ[ℂ] H)) ≤ M := by sorry
