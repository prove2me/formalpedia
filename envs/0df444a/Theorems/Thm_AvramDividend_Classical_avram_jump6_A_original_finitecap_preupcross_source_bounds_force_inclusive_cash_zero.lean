-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_finitecap_preupcross_source_bounds_force_inclusive_cash_zero
-- name    : AvramDividend.Classical.avram_jump6_A_original_finitecap_preupcross_source_bounds_force_inclusive_cash_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:40:19.412183+00:00
-- url     : https://prove2.me/theorems/6622b744-f7fa-45c0-be23-e19fafaf308e
-- title:
--   Original finite-cap source tube prevents upcrossing and forces inclusive stopped barrier cash zero
-- statement:
--   For the genuine spectrally negative Lévy path and admissible finite-cap barrier dividend strategy, if the reserve driving path X.X_s stays at most the distance a−x up to the stopped clock σ, then σ cannot exceed the exact finite first strict upper-exit clock u, so the actual right-closed paymentTimes(ruin)∩Iic(σ) discounted Stieltjes cash integral is zero. Uses previously Proved original barrier pre-upcrossing inclusive cash lemma ece1f923; no synthetic gains, no invalid post-ruin payment atom. This is a key source for the genuine small Brownian tube+early negative mark ruin countermodel to the unit-fullmark physical ledger.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_finitecap_preupcross_source_bounds_force_inclusive_cash_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω) (u σ : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    (hBound : ∀ s : ℝ≥0, s ≤ σ → X.X s ω ≤ a - x)
    (q : ℝ) :
    (∫⁻ s in paymentTimes (ruinTime X x (barrierStrategy X x a) ω) ∩ Iic (σ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure (barrierStrategy X x a) ω)) = 0 := by sorry
