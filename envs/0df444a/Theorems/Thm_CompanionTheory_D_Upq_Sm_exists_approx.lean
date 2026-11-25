-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Sm_exists_approx
-- name    : CompanionTheory.D.Upq.Sm.exists_approx
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:41:39.961193+00:00
-- url     : https://prove2.me/theorems/b02d492a-1ef5-4751-bda0-3b6bd15c7755
-- title:
--   Sm: exists approx
-- statement:
--   The Sm construction uses the exists approx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/IntegralMemOfIsClosed.lean#L282-L385
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/IntegralMemOfIsClosed.lean#L282-L385

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_ModExists
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
open PI CompanionTheory.D.Upq.ModEx
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}
variable {hG : IsMatGroup G}
variable [CompleteSpace H]

theorem CompanionTheory.D.Upq.Sm.exists_approx (hG : IsMatGroup G) (h : RepOn G σ) (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖)
    {w : H} (hw : IsSm G σ w) (hd : Dense (orbSpan G σ w : Set H)) {x : H} (hx : IsSm G σ x)
    {ι : Type} [Fintype ι] {W : ι → List (Mat n)} (hW : ∀ i, LieW G (W i)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ y ∈ orbSpan G σ w, ∀ i, ‖dsW σ (W i) (x - y)‖ < δ := by sorry
