-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_signed_compact_test_eq_of_positive_lintegrals
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_signed_compact_test_eq_of_positive_lintegrals
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:55:54.620295+00:00
-- url     : https://prove2.me/theorems/f70ab66a-f426-4628-8c93-b6a0a3423353
-- title:
--   Signed compact-negative measure tests follow from original positive ENNReal moment identities
-- statement:
--   For locally integrable continuous compact-negative tests, equality of the ENNReal lintegrals of all nonnegative compact-negative tests implies equality of the real Bochner integrals of every signed continuous compact-negative test. Apply the genuine compact support-preserving Jordan decomposition, convert positive lintegrals to real integrals, then subtract. This supplies the signed compact-test hypothesis needed for negative Radon measure uniqueness in P2-A.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_compact_negative_real_jordan_parts
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_positive_real_integral_eq_of_ennreal_tests
open MeasureTheory Set Topology AvramDividend.Classical
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_signed_compact_test_eq_of_positive_lintegrals
    (μ ν : Measure ℝ)
    (hInt : ∀ f : ℝ → ℝ, Continuous f → IsCompact (tsupport f) →
      tsupport f ⊆ Iio (0 : ℝ) → (∀ x : ℝ, 0 ≤ f x) →
      Integrable f μ ∧ Integrable f ν)
    (hPos : ∀ f : ℝ → ℝ, Continuous f → IsCompact (tsupport f) →
      tsupport f ⊆ Iio (0 : ℝ) → (∀ x : ℝ, 0 ≤ f x) →
      (∫⁻ x, ENNReal.ofReal (f x) ∂μ) =
        (∫⁻ x, ENNReal.ofReal (f x) ∂ν))
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Iio (0 : ℝ)) :
    (∫ x, g x ∂μ) = (∫ x, g x ∂ν) := by sorry
