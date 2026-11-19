-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_stopped_HJB_drift_sign_and_zero_clock
-- name    : AvramDividend.Classical.avram_jump6_B_original_stopped_HJB_drift_sign_and_zero_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T18:57:03.800214+00:00
-- url     : https://prove2.me/theorems/38d1c370-7de8-47b1-b12a-c8b06bf664e2
-- title:
--   True original discounted stopped generator drift has nonpositive sign and zero-clock support
-- statement:
--   For the original spectrally negative Levy X and original rightLimit dividend process D, the discounted stopped physical HJB generator drift integrated against a clock measure with no atom at time zero is pathwise nonpositive. It vanishes identically when sigma=0. This establishes the true generator remainder sign and initial support for the mixed all-cap infinite-activity source; it makes no assumptions on finite jump activity or independent noise, and does not assert integrability in probability or a full Ito-Meyer identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_stopped_HJB_drift_sign_and_zero_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (D : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0)
    (μ : Measure ℝ≥0) (hμ0 : μ {(0 : ℝ≥0)} = 0) :
    let Y : ℝ≥0 → Ω → ℝ := fun t ω =>
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t
    let G : Ω → ℝ := fun ω => ∫ t : ℝ≥0,
      if 0 < Y t ω ∧ ENNReal.ofReal (Y t ω) < C ∧ t ≤ σ ω then
        Real.exp (-(q * (t : ℝ))) *
          (X.generator w (Y t ω) - q * w (Y t ω))
      else 0 ∂μ
    ∀ ω, G ω ≤ 0 ∧ (σ ω = 0 → G ω = 0) := by sorry
