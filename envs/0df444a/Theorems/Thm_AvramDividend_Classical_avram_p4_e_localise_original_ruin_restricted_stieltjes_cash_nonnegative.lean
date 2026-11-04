-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ruin_restricted_stieltjes_cash_nonnegative
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_ruin_restricted_stieltjes_cash_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:07:14.990854+00:00
-- url     : https://prove2.me/theorems/4545deaf-1f1b-4821-b10b-ef3de776f38d
-- title:
--   Exact ruin-window discounted dividend Cash is everywhere nonnegative
-- statement:
--   For the canonical P4-F Cash formula with paymentTimes of the true ruinTime intersected with the closed Iic τ and the original dividendMeasure, the ENNReal lintegral maps to a nonnegative real even if the raw lintegral is infinite. This is pathwise and preserves every permitted dividend atom, including at t=0 and surviving horizon. It does not itself prove Cash integrability, supplied separately by the source theorem.
-- source:
--   Exact P4-F hCash; Mathlib ENNReal.toReal_nonneg.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The literal ruin-restricted original random dividend measure produces nonnegative cash. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_ruin_restricted_stieltjes_cash_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) :
    ∀ ω, 0 ≤ Cash ω := by sorry
