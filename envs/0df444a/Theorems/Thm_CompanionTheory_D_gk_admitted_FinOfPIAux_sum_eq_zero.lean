-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_sum_eq_zero
-- name    : CompanionTheory.D.gk.admitted.FinOfPIAux.sum_eq_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:30:16.496072+00:00
-- url     : https://prove2.me/theorems/4d3f0113-0aa5-4cb9-a7f6-5f64a9ae632b
-- title:
--   Fin Of PIAux: sum eq zero
-- statement:
--   The Fin Of PIAux construction uses the sum eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/FinOfPI.lean#L114-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/FinOfPI.lean#L114-L135

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

theorem CompanionTheory.D.gk.admitted.FinOfPIAux.sum_eq_zero (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖)
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, σ g v ∈ S) → S = ⊥ ∨ S = ⊤)
    (L : ι → H →L[ℂ] H) (y : ι → H) (h : ∀ g, ∑ k, L k (σ g (y k)) = 0) (T : H →L[ℂ] H) :
    ∑ k, L k (T (y k)) = 0 := by sorry
