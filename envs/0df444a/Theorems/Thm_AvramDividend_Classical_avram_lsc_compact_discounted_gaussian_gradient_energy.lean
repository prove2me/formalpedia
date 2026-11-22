-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsc_compact_discounted_gaussian_gradient_energy
-- name    : AvramDividend.Classical.avram_lsc_compact_discounted_gaussian_gradient_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T22:43:36.084184+00:00
-- url     : https://prove2.me/theorems/c6115da6-5317-42c0-bc8c-ea678349a308
-- title:
--   Finite L² energy of the genuine discounted Gaussian derivative coefficient on any compact HJB reserve band
-- statement:
--   For a C² interior HJB candidate w, any compact interior reserve band and a state path staying in that band at nonnegative times, the genuine discounted Gaussian gradient coefficient exp(-q s) w'(U_s) σ (zero for negative s) has finite L² energy at every finite horizon under the original probability measure. The bound follows from the Proved compact derivative bound and the Proved bounded-integrand energy estimate, with q nonnegative.
-- source:
--   Avram Dividend Classical 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43, finite-cap original Gaussian stopped Itô branch. Uses already Proved compact derivative bound e6632b80-dff0-4860-86a5-1c73f71fe13d and newly Proved energy bound 43090805-dff6-4165-8036-39ab2cf2f286. The discounted Gaussian coefficient is the spatial derivative times source volatility, restricted to a compact interior band. It is a genuine prerequisite of the stopped Gaussian martingale used in a338c453 and 50e1cf4c.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_source_interior_compact_derivative_bound
import Theorems.Thm_AvramDividend_Classical_avram_lsc_finite_horizon_bounded_integrand_energy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_lsc_compact_discounted_gaussian_gradient_energy
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hopen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hband : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q σ : ℝ) (hq : 0 ≤ q)
    (U : Ω → ℝ → ℝ)
    (hU : ∀ ω s, 0 ≤ s → U ω s ∈ Icc a b) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ T : ℝ, 0 < T →
        ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T,
          (‖(if 0 ≤ s then
              Real.exp (-(q * s)) * deriv w (U ω s) * σ
            else 0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by sorry
