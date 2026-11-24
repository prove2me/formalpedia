-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_Poul_exists_isBump
-- name    : CompanionTheory.D.gk.Poul.exists_isBump
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:33:10.699672+00:00
-- url     : https://prove2.me/theorems/14aded5d-7348-47f1-81ac-2e1f2795f884
-- title:
--   Poul: exists is Bump
-- statement:
--   The Poul construction uses the exists is Bump property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/HaarBumpFunctions/ExistsIsBump.lean#L29-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/HaarBumpFunctions/ExistsIsBump.lean#L29-L44

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

theorem CompanionTheory.D.gk.Poul.exists_isBump (hG : IsMatGroup G) (θ : Mat n →L[ℝ] Mat n) (hθ : ∀ x ∈ G, θ x = x⁻¹) {V : Set (MG G hG)}
    (hV : V ∈ 𝓝 (1 : MG G hG)) : ∃ φ, IsBump G φ ∧ ∀ x : MG G hG, φ x.mat ≠ 0 → x ∈ V := by sorry
