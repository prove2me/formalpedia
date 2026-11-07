-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_zero_clock_exact_physical_F_le
-- name    : AvramDividend.Classical.avram_ubv_loc6_original_zero_clock_exact_physical_F_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:31:54.934227+00:00
-- url     : https://prove2.me/theorems/581f5b9e-b332-4076-a4a9-e41cb0b742b1
-- title:
--   Exact original stopped payoff F at time zero respects initial HJB value including closed cash atom
-- statement:
--   For the actual Levy reserve/right-limit original dividend F k with closed paymentTimes ∩ Iic at σ k, show the pointwise bound F k ω ≤ w x whenever σ k ω = 0. This includes the initial right-dividend atom even on immediate ruin. Derive from the Proved source theorem a2629a86 without any probabilistic approximation or alternate reward convention.
-- source:
--   Source-exact sigma/F specialisation of Proved avram_ubv_hor3_original_zero_clock_term_cash_pathwise_le (a2629a86), by choosing W,Cash,Term from the identical original functions at sigma k; no additional stochastic or cap hypotheses.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_loc6_original_zero_clock_exact_physical_F_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (k : ℕ) (ω : Ω) (hzero : σ k ω = 0) :
    F k ω ≤ w x := by sorry
