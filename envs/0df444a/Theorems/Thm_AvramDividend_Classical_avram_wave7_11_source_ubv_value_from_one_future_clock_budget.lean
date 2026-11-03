-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_source_ubv_value_from_one_future_clock_budget
-- name    : AvramDividend.Classical.avram_wave7_11_source_ubv_value_from_one_future_clock_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:25:56.660878+00:00
-- url     : https://prove2.me/theorems/c6a91a53-0b4e-47f2-b7c0-2ef3e63200ec
-- title:
--   Canonical corrected UBV finite horizon value from one future original ruin-clock budget
-- statement:
--   Under the exact canonical UBV verification hypotheses (original spectrally negative Lévy X, standing law P and filtration, positive cap, original HJB generator, C² interior, w(0)≥0, admissible dividend strategy, nonnegative initial x and horizon T), it is sufficient to know one bounded original ruin-clock expectation inequality at a natural clock n>T when x>0. At x=0 the corrected exact original Stieltjes zero-initial bound supplies the conclusion unconditionally. The theorem concludes the exact original finite-horizon value inequality while retaining the true horizon dividend atom, with no uniform-in-n assumption or auxiliary process.
-- source:
--   Proved corrected zero-initial UBV theorem 14599b22, Proved source HJB side conditions d307095e, and Proved one-future-natural budget bridge 78b21fe9. This isolates the minimal remaining positive-start stochastic obligation for W7-08/W7-12.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_stochastic_core_side_conditions
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_corrected_ubv_zero_initial_all_caps_exact_stieltjes_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_one_future_natural_ruin_clock_budget_controls_full_finite_horizon
import Mathlib.Data.Real.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_source_ubv_value_from_one_future_clock_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T)
    (hOneClock : 0 < x →
      ∃ n : ℕ, T < (n : ℝ) ∧
        (∫⁻ ω, ∫⁻ t in paymentTimes
          (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
          ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
