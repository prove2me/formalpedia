-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_proj_comm
-- name    : CompanionTheory.D.gk.admitted.FinOfPIAux.proj_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:30:21.5818+00:00
-- url     : https://prove2.me/theorems/61d8831e-a8e2-42d1-91ff-15ed59807895
-- title:
--   Fin Of PIAux: proj comm
-- statement:
--   The Fin Of PIAux construction uses the proj comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/FinOfPI.lean#L77-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/FinOfPI.lean#L77-L88

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
omit [CompleteSpace H] [DecidableEq ι]

theorem CompanionTheory.D.gk.admitted.FinOfPIAux.proj_comm (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖)
    (C : Submodule ℂ (PiLp 2 (fun _ : ι => H))) [C.HasOrthogonalProjection]
    (hC : ∀ g, ∀ z ∈ C, diag (σ g) z ∈ C) (g : G) (z : PiLp 2 (fun _ : ι => H)) :
    C.starProjection (diag (σ g) z) = diag (σ g) (C.starProjection z) := by sorry
