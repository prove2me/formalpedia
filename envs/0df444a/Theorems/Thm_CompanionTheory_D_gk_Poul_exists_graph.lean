-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_Poul_exists_graph
-- name    : CompanionTheory.D.gk.Poul.exists_graph
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:52.975867+00:00
-- url     : https://prove2.me/theorems/8fe8aa59-e56a-49cd-958a-780204b26657
-- title:
--   Poul: exists graph
-- statement:
--   The Poul construction uses the exists graph property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/HaarBumpFunctions/ExistsOpOfForm.lean#L22-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/HaarBumpFunctions/ExistsOpOfForm.lean#L22-L76

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

theorem CompanionTheory.D.gk.Poul.exists_graph (hiso : ∀ g v, ‖σ g v‖ = ‖v‖) (hiso' : ∀ g v, ‖σ' g v‖ = ‖v‖)
    (hs : ∀ T : H' →L[ℂ] H', (∀ g v, T (σ' g v) = σ' g (T v)) → ∃ c : ℂ, ∀ v, T v = c • v)
    (Γ : Submodule ℂ (H' × H)) (hcl : IsClosed (Γ : Set (H' × H))) (hinv : ∀ g, ∀ p ∈ Γ, (σ' g p.1, σ g p.2) ∈ Γ)
    {y₀ : H'} {z₀ : H} (h₀ : (y₀, z₀) ∈ Γ) (hy₀ : y₀ ≠ 0) :
    ∃ T : H' →L[ℂ] H, (∀ g y, T (σ' g y) = σ g (T y)) ∧ ∀ y, (y, T y) ∈ Γ := by sorry
