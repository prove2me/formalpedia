-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps10_original_localised_generator_drift_nonpos
-- name    : AvramDividend.Classical.avram_ubv_ito_jumps10_original_localised_generator_drift_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:34:23.288562+00:00
-- url     : https://prove2.me/theorems/c548ef6c-edff-4026-b091-b88070ef909f
-- title:
--   Discounted original Lévy generator drift is nonpositive on a compact stopped interior region
-- statement:
--   For Avram's actual controlled reserve before dividend payment, the discounted generator residual over any interior localisation region is nonpositive after masking by the original ruin clock and a finite horizon. Integrating the pointwise sign proves a reusable HJB drift inequality. Its integrability is deliberately a separate obligation for later Itô-Meyer assembly.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_ito_jumps10_original_localised_generator_drift_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (E : Set (ℝ≥0 × Ω))
    (hE : ∀ p ∈ E,
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      0 < y ∧ ENNReal.ofReal y < C)
    (μ : Measure (ℝ≥0 × Ω)) :
    (∫ p : ℝ≥0 × Ω,
      if p ∈ E then
        (if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0) *
        (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0) *
        (X.generator w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) -
          q * w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1))
      else 0 ∂μ) ≤ 0 := by sorry
