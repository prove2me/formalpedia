-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a275_original_gaussian_true_physical_signed_exponential_tail_expected_L1
-- name    : AvramDividend.Classical.avram_ga_a275_original_gaussian_true_physical_signed_exponential_tail_expected_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:31:11.203467+00:00
-- url     : https://prove2.me/theorems/9a5ebcbc-d2da-4a4a-b472-4ce63b399076
-- title:
--   Original signed rare Gaussian fullcell exponential endpoint expected L1 vanishes from positive exp and raw-square Gaussian tails
-- statement:
--   For the actual original zerojump Gaussian physical grid and an original stopping time, the expected finite sum of exp(theta times raw increment) over all wholly pre-stop rare cells |r|≥δ tends to zero as mesh refines, provided each signed rare finite sum is integrable. The original one-sided positive exp tail is already proved a233 and stopped prefix rare square expected L1 already proved a187, and a274 controls the full signed rare endpoint pointwise. This is the source expected control for the original combined large-cell Gaussian a263 verification.
-- source:
--   a274 original source pointwise + a233 positive exp L1 + a187 real raw large-square tail + a273 squeeze

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a274_original_gaussian_true_physical_signed_exponential_tail_pointwise_majorant
import Theorems.Thm_AvramDividend_Classical_avram_ga_a273_expected_positive_small_upper_integrable_two_sources_L1
import Theorems.Thm_AvramDividend_Classical_avram_ga_a233_original_stopped_fullcell_positive_raw_gaussian_exponential_tail_expected_L1_vanish
import Theorems.Thm_AvramDividend_Classical_avram_ga_a186_original_stopped_Gaussian_raw_large_tail_real_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a187_original_stopped_Gaussian_raw_large_tail_real_L1_vanish
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a275_original_gaussian_true_physical_signed_exponential_tail_expected_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (n : ℕ) (hn : 0 < n) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (theta delta : ℝ) (hθ : 0 ≤ theta) (hδ : 0 < delta) :
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0)+1)
    let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0)*Δ m
    let R : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X (s m i+Δ m) ω-X.X (s m i) ω
    let Signed : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ Finset.range m,
        if (s m i < ρ ω ∧ s m i+Δ m ≤ ρ ω) ∧ delta ≤ |R m i ω|
        then Real.exp (theta*R m i ω) else 0
    (∀ m, Integrable (Signed m) P) →
      Tendsto (fun m => ∫ ω, Signed m ω ∂P)
        atTop (𝓝 (0 : ℝ)) := by sorry
