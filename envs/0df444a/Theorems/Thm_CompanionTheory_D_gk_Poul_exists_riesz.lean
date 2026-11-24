-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_Poul_exists_riesz
-- name    : CompanionTheory.D.gk.Poul.exists_riesz
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:33:31.557093+00:00
-- url     : https://prove2.me/theorems/b73fb7dc-b026-48e5-8bfc-998d9c14b79e
-- title:
--   Poul: exists riesz
-- statement:
--   The Poul construction uses the exists riesz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/HaarBumpFunctions/ExistsIsBump.lean#L195-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/HaarBumpFunctions/ExistsIsBump.lean#L195-L210

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

theorem CompanionTheory.D.gk.Poul.exists_riesz (ha : ∀ x y, IsSm G σ x → IsSm G σ y → l (x + y) = l x + l y)
    (hs : ∀ (c : ℂ) x, IsSm G σ x → l (c • x) = c * l x) {D : ℝ} (hD : ∀ x, IsSm G σ x → ‖l x‖ ≤ D * ‖x‖) :
    ∃ z : H, ∀ x, IsSm G σ x → l x = ⟪z, x⟫_ℂ := by sorry
