-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a188_original_stopped_Gaussian_raw_tail_lintegral_zero
-- name    : AvramDividend.Classical.avram_ga_a188_original_stopped_Gaussian_raw_tail_lintegral_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T15:57:45.047372+00:00
-- url     : https://prove2.me/theorems/bd2a2c52-ec62-4fc4-9a21-e42638936887
-- title:
--   Original stopped Gaussian raw large-tail real-sum extended expectation tends to zero
-- statement:
--   For the original zero-jump Gaussian Lévy process and true stopping clock, form the real-valued finite sum of squared raw physical source increments restricted to a large threshold on pre-stop cells. The extended nonnegative expectation of this exact real sum tends to zero. This is a source-faithful finite-sum conversion of the already Proved original Gaussian tail theorem ga56 and is the ENNReal premise of a184 for the real Taylor L1 estimate.
-- source:
--   Proved ga56 original Gaussian stopped raw source tail ENNReal limit, ofReal_sum_of_nonneg.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a56_original_stopped_raw_large_tail_tendsto
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a188_original_stopped_Gaussian_raw_tail_lintegral_zero
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
    Tendsto (fun m => ∫⁻ ω, ENNReal.ofReal (Tail m ω) ∂P)
      atTop (𝓝 (0 : ℝ≥0∞)) := by sorry
