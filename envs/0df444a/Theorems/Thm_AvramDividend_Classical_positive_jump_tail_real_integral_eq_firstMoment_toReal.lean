-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_jump_tail_real_integral_eq_firstMoment_toReal
-- name    : AvramDividend.Classical.positive_jump_tail_real_integral_eq_firstMoment_toReal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:01:48.562511+00:00
-- url     : https://prove2.me/theorems/96049a92-cca2-4023-a9f7-a6218f675682
-- title:
--   Exact real layer-cake mass identity for positive strict jump-tail densities
-- statement:
--   For a nonnegative jump-magnitude measure with finite first moment, the real positive-time Lebesgue integral of its strict upper-tail mass equals the toReal of the first-moment lintegral. The Proved layer-cake identity determines the extended-real mass, the sharp Markov bound ensures pointwise finiteness at every positive threshold, and the Proved real L1 theorem permits conversion using ofReal_integral_eq_lintegral_ofReal. This is the exact normalised-kernel mass equation required by the cstar-connected bounded-variation Esscher renewal series identification.
-- source:
--   Proved positive_jump_tail_density_total_mass, positive_jump_tail_threshold_mass_le_first_moment, positive_jump_tail_real_integrable_of_finite_firstMoment; Mathlib ofReal_integral_eq_lintegral_ofReal.

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_density_total_mass
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_threshold_mass_le_first_moment
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_real_integrable_of_finite_firstMoment
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.positive_jump_tail_real_integral_eq_firstMoment_toReal
    (μ : Measure ℝ≥0)
    (hfirst : (∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μ) < ⊤) :
    (∫ t in Ioi (0 : ℝ),
      (μ {z : ℝ≥0 | t < (z : ℝ)}).toReal ∂volume) =
      (∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μ).toReal := by sorry
