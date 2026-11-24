-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_Poul_IsSmForm_avg_bd
-- name    : CompanionTheory.D.gk.Poul.IsSmForm.avg_bd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:33:33.026844+00:00
-- url     : https://prove2.me/theorems/698c6e85-3bb2-4596-8ce2-405ea7119304
-- title:
--   Is Sm Form: avg bd
-- statement:
--   The Is Sm Form construction uses the avg bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/HaarBumpFunctions/ExistsIsBump.lean#L138-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/HaarBumpFunctions/ExistsIsBump.lean#L138-L171

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

theorem CompanionTheory.D.gk.Poul.IsSmForm.avg_bd (hl : IsSmForm G σ W C l) (h : RepOn G σ) (hW : ∀ i, LieW G (W i)) {v : H}
    (hv : IsSm G σ v) {φ : Mat n → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) {x : H} (hx : IsSm G σ x) :
    ‖(∫ g : MG G hG, φ g.mat • l (σ g.mat v) ∂haar) - l x‖ ≤
      C * ∑ i, ‖(∫ g : MG G hG, φ g.mat • dsW σ (W i) (σ g.mat v) ∂haar) - dsW σ (W i) x‖ := by sorry
