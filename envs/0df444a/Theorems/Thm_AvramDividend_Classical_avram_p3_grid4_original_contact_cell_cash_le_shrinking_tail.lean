-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_contact_cell_cash_le_shrinking_tail
-- name    : AvramDividend.Classical.avram_p3_grid4_original_contact_cell_cash_le_shrinking_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T20:27:59.29824+00:00
-- url     : https://prove2.me/theorems/ccfcad13-2846-4f09-9f83-6a159f5301f1
-- title:
--   Original stopped crossing-cell discounted cash bounded by a shrinking real ruin/horizon tail
-- statement:
--   For the actual original X/D ruin/horizon-clamped physical clock, the proven deterministic mesh-width bound 4ded2370 implies that the unique contact-cell left endpoint is at least tau minus T/(m+1). Its genuine paymentTimes-restricted discounted dividendMeasure cash is therefore no larger than the original measure of that deterministic-width terminal tail. This is the missing source-faithful domination step for taking the contact-cell limit. It makes no claim that the tail vanishes without the ruin-atom exclusion or that a surviving horizon T atom is zero. The subsequent limit uses the separate original paymentTimes ruin and horizon accounting lemmas.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_physical_cell_length_le
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_contact_cell_cash_le_shrinking_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q : ℝ)
    (T : ℝ≥0) (m i : ℕ) (hi : i < m + 1) (ω : Ω) :
    let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
    u (i + 1) = τ →
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioc (u i : ℝ) (u (i + 1) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioc ((τ - T / (m + 1) : ℝ≥0) : ℝ) (τ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
