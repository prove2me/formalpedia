-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_Poul_IsInv_exists_rep
-- name    : CompanionTheory.D.gk.Poul.IsInv.exists_rep
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:33:57.294808+00:00
-- url     : https://prove2.me/theorems/7df7bc64-dd70-4525-a197-60f6d15c3698
-- title:
--   Is Inv: exists rep
-- statement:
--   The Is Inv construction uses the exists rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/HaarBumpFunctions/ExistsIsBump.lean#L248-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/HaarBumpFunctions/ExistsIsBump.lean#L248-L277

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

theorem CompanionTheory.D.gk.Poul.IsInv.exists_rep [(haar : Measure (MG G hG)).IsInvInvariant] (θ : Mat n →L[ℝ] Mat n)
    (hθ : ∀ x ∈ G, θ x = x⁻¹) (hB : IsInv G σ σ' W W' C B) (h : RepOn G σ) (h' : RepOn G σ')
    (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖) (hc' : ∀ v, ContinuousOn (fun g => σ' g v) G)
    (hW : ∀ i, LieW G (W i)) (hW' : ∀ j, LieW G (W' j)) [Nontrivial H'] :
    ∃ y₀ z₀, IsSm G σ' y₀ ∧ y₀ ≠ 0 ∧ ∀ x, IsSm G σ x → B x y₀ = ⟪z₀, x⟫_ℂ := by sorry
