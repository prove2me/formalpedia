-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_Poul_IsSmForm_sub
-- name    : CompanionTheory.D.gk.Poul.IsSmForm.sub
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:37:05.283887+00:00
-- url     : https://prove2.me/theorems/36e5894f-5c6d-438b-b5e5-7e3c957e518d
-- title:
--   Is Sm Form: sub
-- statement:
--   The Is Sm Form construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/HaarBumpFunctions/ExistsIsBump.lean#L118-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/HaarBumpFunctions/ExistsIsBump.lean#L118-L121

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsOpOfForm
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Garding
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_sub

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
omit [CompleteSpace H]

theorem CompanionTheory.D.gk.Poul.IsSmForm.sub (hl : IsSmForm G σ W C l) {x y : H} (hx : IsSm G σ x) (hy : IsSm G σ y) :
    l (x - y) = l x - l y := by sorry
