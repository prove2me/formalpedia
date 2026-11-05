-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_positive_horizon_pair_mean
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_positive_horizon_pair_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:52:59.839202+00:00
-- url     : https://prove2.me/theorems/978af370-ca46-4733-98ff-bb2325eb7606
-- title:
--   Positive physical-horizon original chronological marked pair mean from uniform-grid source compensation
-- statement:
--   For the actual original Lévy negative-band marked times, on strictly positive physical horizon, the chronological pair count is real L1 and has twice its mean equal to the square of original horizon times ν mass. Requires original predictable rectangular compensation, a uniform finite-grid lift, and monotone convergence; no surrogate Poisson model. This separates the genuinely stochastic T>0 step from an accepted unconditional T=0 source case.
-- source:
--   Existing original d938e9a5 statement, Proved zero branch 813af4ea; Proved physical finite-cell 284b2602, ceiling-grid equality components c7fa6a87, 0ecd8bf1, ddbdde55, 6bdc2c26, source monotone refinement; pinned Mathlib.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_positive_horizon_pair_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let K : Ω → ℕ := fun ω =>
      ((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card
    let r : ℝ :=
      (((T : ℝ≥0) : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => 2 * (K ω : ℝ)) P ∧
    (∫ ω, 2 * (K ω : ℝ) ∂P) = r ^ 2 := by sorry
