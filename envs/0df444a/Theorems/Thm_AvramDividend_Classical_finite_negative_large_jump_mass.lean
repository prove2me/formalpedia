-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_negative_large_jump_mass
-- name    : AvramDividend.Classical.finite_negative_large_jump_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T22:51:29.076992+00:00
-- url     : https://prove2.me/theorems/6ab1f03e-7308-40c9-9e93-05203acd70a7
-- title:
--   Finite large-jump mass from the Lévy measure quadratic-integrability condition
-- statement:
--   Any Lévy jump measure with finite integral of min(1,y²) has finite mass on the negative half-line y≤−1. On that set min(1,y²)=1, and the restricted integral is bounded by the global Lévy-integrability integral. This proves the large-jump half of the finite truncated-first-moment condition required to push negative jumps forward to positive jump magnitudes in the bounded-variation renewal construction.
-- source:
--   Classical SpectrallyNegativeLevy.ν_integrable, pinned Mathlib setLIntegral_congr_fun, setLIntegral_const, setLIntegral_le_lintegral

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- Lévy integrability implies finite mass of negative jumps of magnitude
at least one, independent of bounded variation. -/
theorem finite_negative_large_jump_mass (ν : Measure ℝ)
    (hν : (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) < ⊤) :
    ν (Iic (-1 : ℝ)) < ⊤ := by
  sorry

end AvramDividend.Classical
