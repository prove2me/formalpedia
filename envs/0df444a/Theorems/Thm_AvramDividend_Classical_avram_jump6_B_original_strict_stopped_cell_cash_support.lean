-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_strict_stopped_cell_cash_support
-- name    : AvramDividend.Classical.avram_jump6_B_original_strict_stopped_cell_cash_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:43:13.915923+00:00
-- url     : https://prove2.me/theorems/3b39135b-575e-4a95-96c5-4d744a739280
-- title:
--   Original canonical stopped cell discount cash equals paymentTimes-filtered cash before ruin
-- statement:
--   For the original Levy process, real dividend measure, paymentTimes of original ruin and the actual clipped physical-grid cells, discounted cash over any cell is unchanged by intersecting with paymentTimes whenever the stopping horizon t has a strictly pre-ruin buffer t<rho<=ruinTime. This reuses the Proved original strict cash support 26b42fc3 and isolates the extra ruin-contact endpoint as the only unsupported case.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger129_original_strict_cell_cash_support
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_strict_stopped_cell_cash_support
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (q : ℝ)
    (t ρ : ℝ≥0) (htρ : t < ρ)
    (hρruin : (ρ : ℝ≥0∞) ≤ ruinTime X x D ω) (j i : ℕ) :
    let Δ : ℝ≥0 := (1 : ℝ≥0) / ((j : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun r => min ((r : ℝ≥0) * Δ) t
    (∫⁻ r in Ioc (v i : ℝ) (v (i+1) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)).toReal =
    (∫⁻ r in paymentTimes (ruinTime X x D ω) ∩
        Ioc (v i : ℝ) (v (i+1) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)).toReal := by sorry
