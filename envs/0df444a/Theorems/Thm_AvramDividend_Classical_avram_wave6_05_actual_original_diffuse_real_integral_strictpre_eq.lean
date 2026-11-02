-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_original_diffuse_real_integral_strictpre_eq
-- name    : AvramDividend.Classical.avram_wave6_05_actual_original_diffuse_real_integral_strictpre_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:52:14.870389+00:00
-- url     : https://prove2.me/theorems/2ef77788-f299-415a-ad56-c03220c46992
-- title:
--   Actual original Stieltjes atomless real signed derivative integral equals strict original Lévy source-prejump derivative integral
-- statement:
--   For any actual admissible left-continuous finite-variation dividend strategy and every finite horizon, the genuine original dividendMeasure restricted to [0,T] admits its countable atomic plus atomless decomposition. Against the actual atomless dividend component, the real Bochner set integral over positive times of e^-qs(1-w'(U_s)) equals exactly the same integral with the genuine original strict source-prejump surplus x+leftLim X_s-rightLimit D_s in the derivative argument. This is an exact equality for any w and real q, with no regularity, finite-jump or summability assumption on the dividend control. It is stronger in sign-sensitive applications than equality of ENNReal.ofReal gradient lower integrals, and remains true with singular-continuous dividend mass because the actual atomless component ignores countably many source and dividend jump times. The time-zero payment atom is excluded by Ioi 0 and handled separately by caplinear V.
-- source:
--   Existing canonically Proved original dividendMeasure atomic/atomless a.e. strict source-prejump reserve identification and pinned MeasureTheory.setIntegral_congr_ae, specialised to real signed discounted derivative integrands.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_actual_dividend_diffuse_preserves_strict_source_prejump_ae

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_05_actual_original_diffuse_real_integral_strictpre_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (ω : Ω) (T : ℝ≥0) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧
      μatom = Measure.sum (fun t : A => μ {(t : ℝ)} • Measure.dirac (t : ℝ)) ∧
      μatom Aᶜ = 0 ∧ NullSingletonClass μdiffuse ∧
      (∀ t : ℝ≥0, t ≤ T →
        μ {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
      (∀ (w : ℝ → ℝ) (q : ℝ),
        (∫ s in Ioi (0 : ℝ),
          Real.exp (-(q * s)) *
            (1 - deriv w (riskProcess X x D s.toNNReal ω)) ∂μdiffuse) =
        (∫ s in Ioi (0 : ℝ),
          Real.exp (-(q * s)) *
            (1 - deriv w (x +
              Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
              rightLimit D s.toNNReal ω)) ∂μdiffuse)) := by sorry
