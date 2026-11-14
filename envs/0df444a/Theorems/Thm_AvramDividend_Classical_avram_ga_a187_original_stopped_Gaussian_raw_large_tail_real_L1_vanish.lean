-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a187_original_stopped_Gaussian_raw_large_tail_real_L1_vanish
-- name    : AvramDividend.Classical.avram_ga_a187_original_stopped_Gaussian_raw_large_tail_real_L1_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:06:41.392354+00:00
-- url     : https://prove2.me/theorems/38eb20fa-b328-47ac-bc0e-469e33dce120
-- title:
--   Original stopped physical Gaussian raw large-square tail tends to zero in ordinary expected L1
-- statement:
--   For the original spectrally negative zero-jump Gaussian Lévy source with positive Gaussian scale, uniform deterministic mesh and genuine stopping clock, the real expectation of the sum of raw source squared increments restricted to a fixed positive large-increment threshold and the stopped prefix tends to zero. Reuses Proved ga56's source-exact ENNReal limit plus a186 integrability and a184 real limit bridge. This is the genuine original Gaussian large raw tail required by the classical Taylor remainder a149.
-- source:
--   Proved a56 source stopped raw tail ENNReal limit; a186 original real integrability; a184 ENNReal-to-real expected limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a56_original_stopped_raw_large_tail_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_ga_a184_nonnegative_real_expected_L1_zero_of_extended_integral_zero
import Theorems.Thm_AvramDividend_Classical_avram_ga_a186_original_stopped_Gaussian_raw_large_tail_real_integrable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a187_original_stopped_Gaussian_raw_large_tail_real_L1_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (η : ℝ) (hη : 0 < η) :
    let Tail : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let r : ℝ := X.X (s + Δ) ω - X.X s ω
        if s < ρ ω then (if η ≤ |r| then r^2 else 0) else 0
    Tendsto (fun m => ∫ ω, Tail m ω ∂P) atTop (𝓝 (0 : ℝ)) := by sorry
