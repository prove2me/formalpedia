-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_mem_unitary
-- name    : CompanionTheory.D.gk.admitted.FinOfPIAux.mem_unitary
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:30:01.869829+00:00
-- url     : https://prove2.me/theorems/608157b8-b65d-4a25-99ee-c6c524cc501b
-- title:
--   Fin Of PIAux: mem unitary
-- statement:
--   The Fin Of PIAux construction uses the mem unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/FinOfPI.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/FinOfPI.lean#L28-L31

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinOfPI
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_mem_unitary

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

theorem CompanionTheory.D.gk.admitted.FinOfPIAux.mem_unitary (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖) (g : G) :
    σ g ∈ unitary (H →L[ℂ] H) := by sorry
