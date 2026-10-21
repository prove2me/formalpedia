-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_uniform_truncated_bounds
-- name    : AvramDividend.Classical.dividendValue_le_of_uniform_truncated_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T10:14:58.812281+00:00
-- url     : https://prove2.me/theorems/dc933bd8-8284-4e80-89e6-304a074e0a4a
-- title:
--   Uniform finite-horizon dividend-value upper bounds imply the full-horizon bound
-- statement:
--   For any admissible dividend strategy and any extended nonnegative constant A, assume its expectation of discounted dividends truncated at each natural-number real horizon n is at most A. Then the full expected dividend value is at most A. Use the previously accepted exact dividendValue_eq_iSup_truncated, which has already discharged path measurability and monotone integration to identify the full value with the supremum of all finite-horizon expectations, and apply the order-theoretic iSup_le. No stochastic HJB bound itself is assumed beyond the explicit finite-horizon inequalities. This provides an exact interface from the missing stopped Lévy–Itô finite-horizon estimate to the published full dividendValue target.
-- source:
--   Previously Proved dividendValue_eq_iSup_truncated and order-theoretic iSup_le, no Open theorem imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendValue_le_of_uniform_truncated_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissible X x D) (A : ℝ≥0∞)
    (hBound : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ A) :
    dividendValue X q x D ≤ A := by sorry
