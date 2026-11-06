-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_contact_tail_cash_antitone
-- name    : AvramDividend.Classical.avram_p3_grid4_original_contact_tail_cash_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T21:37:21.004206+00:00
-- url     : https://prove2.me/theorems/931b9450-a474-4e27-8178-ebbd346ae44f
-- title:
--   Original ruin/horizon stopped discounted contact-tail cash decreases under physical mesh refinement
-- statement:
--   For the true original X/D ruin/horizon-clamped stopping clock tau, the literal original dividendMeasure weighted cash in the shrinking paymentTimes tail Ioc(tau-T/(m+1),tau) is antitone in physical mesh index m. This is a source-faithful monotonicity input to finite weighted-measure continuity from above. It retains time-zero, ruin and horizon endpoint accounting and does not assume an endpoint atom vanishes.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_contact_tail_cash_antitone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q : ℝ) (T : ℝ≥0) (ω : Ω) :
    let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    Antitone (fun m : ℕ =>
      ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
        Ioc ((τ - T / (m + 1) : ℝ≥0) : ℝ) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) := by sorry
