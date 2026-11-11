-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin20_original_true_spatial_clocks_with_cofinality
-- name    : AvramDividend.Classical.avram_mix_fin20_original_true_spatial_clocks_with_cofinality
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T09:05:32.147503+00:00
-- url     : https://prove2.me/theorems/cfcb0f9d-c6cc-4641-8554-43a46d17693c
-- title:
--   Exact original spatial clock certificate for finite mixed stopped Ito localisation
-- statement:
--   Construct the original first-upcross clocks S_k through k+1 and true bounded right-continuous stopping clocks L_k=min(rho,S_k). Verify S threshold monotonicity, pointwise cofinality, original-filtration stopping, domination and eventual exact clock equality, including zero mask. This is the geometric clock component of the physical finite mixed cash ledger.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin20_original_true_upper_exit_spatial_cofinality
import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_record_grid_clocks_eventually_ge_horizon
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin20_original_true_spatial_clocks_with_cofinality
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℝ≥0)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ n) :
    ∃ (S : ℕ → Ω → ℝ≥0∞) (L : ℕ → Ω → ℝ≥0),
      (∀ k ω, S k ω = twoSidedExitUpTime X ((k : ℝ) + 1) ω) ∧
      (∀ ω, Monotone (fun k => S k ω)) ∧
      (∀ ω, (⨆ k : ℕ, S k ω) = ⊤) ∧
      (∀ k ω, L k ω = (min (ρ ω : ℝ≥0∞) (S k ω)).toNNReal) ∧
      (∀ k, IsStoppingTime 𝓕.rightCont
        (fun ω => (L k ω : WithTop ℝ≥0))) ∧
      (∀ k ω, L k ω ≤ ρ ω) ∧
      (∀ ω, ∀ᶠ k : ℕ in atTop, L k ω = ρ ω) := by sorry
