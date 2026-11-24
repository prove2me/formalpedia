-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_Poul_IsSmForm_exists_bd
-- name    : CompanionTheory.D.gk.Poul.IsSmForm.exists_bd
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:33:09.398042+00:00
-- url     : https://prove2.me/theorems/b5be8328-9fad-4378-9ade-9d4a03784097
-- title:
--   Is Sm Form: exists bd
-- statement:
--   The Is Sm Form construction uses the exists bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/HaarBumpFunctions/ExistsIsBump.lean#L181-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/HaarBumpFunctions/ExistsIsBump.lean#L181-L193

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
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mat n → (H →L[ℂ] H)}
variable {ι : Type} [Fintype ι] {W : ι → List (Mat n)} {C : ℝ} {l : H → ℂ}

theorem CompanionTheory.D.gk.Poul.IsSmForm.exists_bd (hl : IsSmForm G σ W C l) (h : RepOn G σ) (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖)
    (hW : ∀ i, LieW G (W i)) {φ : Mat n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∃ D : ℝ, ∀ v, IsSm G σ v → ‖∫ g : MG G hG, φ g.mat • l (σ g.mat v) ∂haar‖ ≤ D * ‖v‖ := by sorry
