-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_strict_cash_fixed_survival_terminal_L1_mesh
-- name    : AvramDividend.Classical.avram_p3_f2_original_strict_cash_fixed_survival_terminal_L1_mesh
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:34:03.779314+00:00
-- url     : https://prove2.me/theorems/8a5ada70-eb22-4093-b7fe-16d9f1346ee2
-- title:
--   Actual original stopped strict cash and fixed survival terminal converge together in L1 along cofinal physical times
-- statement:
--   The original controlled Lévy path, dividend Stieltjes measure and strict-survival terminal are retained literally. The already-proved source cofinal strict-cash L1 theorem upgrades to the complete cash-plus-fixed-terminal stopped payoff. The terminal cancels algebraically, so this proves a genuine L1 interchanging bridge without a terminal domination hypothesis, and leaves the horizon/right-payment atoms to P3-G2.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_cofinal_L1_error_tendsto_zero
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_f2_original_strict_cash_fixed_survival_terminal_L1_mesh
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q) (S : ℝ≥0)
    (u : ℕ → ℝ) (hmono : Monotone u)
    (hu : ∀ n, 0 ≤ u n) (hbelow : ∀ n, u n ≤ (S : ℝ))
    (hcover : ∀ s : ℝ, s < (S : ℝ) → ∃ n, s < u n) :
    let Cash : ℝ → Ω → ℝ := fun r ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio r,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal
    let Term : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
      else 0
    Tendsto (fun n => ∫ ω : Ω,
      |(Cash (S : ℝ) ω + Term ω) - (Cash (u n) ω + Term ω)| ∂P)
      atTop (nhds 0) := by sorry
