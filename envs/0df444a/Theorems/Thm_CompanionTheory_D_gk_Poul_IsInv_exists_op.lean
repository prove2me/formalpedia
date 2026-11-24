-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_Poul_IsInv_exists_op
-- name    : CompanionTheory.D.gk.Poul.IsInv.exists_op
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:33:23.811849+00:00
-- url     : https://prove2.me/theorems/344a87c5-8779-42d3-9edc-f721dc30872d
-- title:
--   Is Inv: exists op
-- statement:
--   The Is Inv construction uses the exists op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/HaarBumpFunctions/ExistsIsBump.lean#L284-L354
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/HaarBumpFunctions/ExistsIsBump.lean#L284-L354

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsOpOfForm
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Garding
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.Poul
open PI CompanionTheory.D.Upq.ModEx CompanionTheory.D.Upq.Sm CompanionTheory.D.gk.admitted CompanionTheory.D.gk.admitted.Gard
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {G : Set (Mat n)} {hG : IsMatGroup G}
variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  {σ : Mat n → (H →L[ℂ] H)} {σ' : Mat n → (H' →L[ℂ] H')}
variable {ι ι' : Type} [Fintype ι] [Fintype ι'] {W : ι → List (Mat n)} {W' : ι' → List (Mat n)} {C : ℝ}
  {B : H → H' → ℂ}

theorem CompanionTheory.D.gk.Poul.IsInv.exists_op [(haar : Measure (MG G hG)).IsInvInvariant] (θ : Mat n →L[ℝ] Mat n)
    (hθ : ∀ x ∈ G, θ x = x⁻¹) (hB : IsInv G σ σ' W W' C B) (h : RepOn G σ) (h' : RepOn G σ')
    (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖) (hiso' : ∀ g ∈ G, ∀ v, ‖σ' g v‖ = ‖v‖)
    (hc : ∀ v, ContinuousOn (fun g => σ g v) G) (hc' : ∀ v, ContinuousOn (fun g => σ' g v) G)
    (hirr : PI.UpqRep.IsIrredOn G σ) (hirr' : PI.UpqRep.IsIrredOn G σ')
    (hW : ∀ i, LieW G (W i)) (hW' : ∀ j, LieW G (W' j)) [Nontrivial H] [Nontrivial H'] :
    ∃ T : H' →L[ℂ] H, (∀ g ∈ G, ∀ y, T (σ' g y) = σ g (T y)) ∧
      ∀ x y, IsSm G σ x → IsSm G σ' y → B x y = ⟪T y, x⟫_ℂ := by sorry
