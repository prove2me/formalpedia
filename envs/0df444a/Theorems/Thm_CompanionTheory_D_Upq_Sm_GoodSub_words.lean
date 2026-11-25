-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Sm_GoodSub_words
-- name    : CompanionTheory.D.Upq.Sm.GoodSub.words
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:14:07.631183+00:00
-- url     : https://prove2.me/theorems/e136ae39-6012-55d9-b2d2-2e0aa3e4a5d7
-- title:
--   Good Sub: words
-- statement:
--   The Good Sub construction uses the words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/UniformCoefficientBounds/CoefBoundUniform.lean#L120-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/UniformCoefficientBounds/CoefBoundUniform.lean#L120-L142

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_QuotInv
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_UniformCoefficientBounds_CoefBoundUniform
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set
open scoped ContDiff InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
open PI
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {G K : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}

theorem CompanionTheory.D.Upq.Sm.GoodSub.words (hG : IsMatGroup G) (h : RepOn G σ) (hK : K ⊆ G) {T : Submodule ℂ H}
    (hT : GoodSub G K σ T) {w : H} (hw : w ∈ T) (m : ℕ) :
    ∃ (T' : Submodule ℂ H) (C : ℝ), GoodSub G K σ T' ∧ 0 ≤ C ∧ ∀ W : List (Mat n), LieW G W →
      (∀ X ∈ W, ‖X‖ ≤ 1) → W.length ≤ m → dsW σ W w ∈ T' ∧ ‖dsW σ W w‖ ≤ C := by sorry
