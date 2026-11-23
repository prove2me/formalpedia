-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_Poul_exists_op_of_form
-- name    : CompanionTheory.D.gk.Poul.exists_op_of_form
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:15.072234+00:00
-- url     : https://prove2.me/theorems/b3d371b9-4bd4-4bde-af5a-3f901a7f15b7
-- title:
--   Poul: exists op of form
-- statement:
--   The Poul construction uses the exists op of form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/HaarBumpFunctions/ExistsOpOfForm.lean#L78-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/HaarBumpFunctions/ExistsOpOfForm.lean#L78-L109

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinOfPI
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsOpOfForm
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
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.Poul
variable {G : Type} [Group G] {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  {σ : G →* (H →L[ℂ] H)} {σ' : G →* (H' →L[ℂ] H')}

theorem CompanionTheory.D.gk.Poul.exists_op_of_form (hiso : ∀ g v, ‖σ g v‖ = ‖v‖) (hiso' : ∀ g v, ‖σ' g v‖ = ‖v‖)
    (hs : ∀ T : H' →L[ℂ] H', (∀ g v, T (σ' g v) = σ' g (T v)) → ∃ c : ℂ, ∀ v, T v = c • v)
    (S : Set H) (S' : Set H') (hS : ∀ g, ∀ x ∈ S, σ g x ∈ S) (hS' : ∀ g, ∀ y ∈ S', σ' g y ∈ S') (B : H → H' → ℂ)
    (hB : ∀ g, ∀ x ∈ S, ∀ y ∈ S', B (σ g x) (σ' g y) = B x y) {y₀ : H'} {z₀ : H} (hy₀S : y₀ ∈ S') (hy₀ : y₀ ≠ 0)
    (h₀ : ∀ x ∈ S, B x y₀ = ⟪z₀, x⟫_ℂ) :
    ∃ T : H' →L[ℂ] H, (∀ g y, T (σ' g y) = σ g (T y)) ∧
      ∀ x ∈ S, ∀ w, (∀ y ∈ S', B x y = ⟪y, w⟫_ℂ) → ∀ y ∈ S', B x y = ⟪T y, x⟫_ℂ := by sorry
