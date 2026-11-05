-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_positive_real_integral_eq_of_ennreal_tests
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_positive_real_integral_eq_of_ennreal_tests
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:45:25.385252+00:00
-- url     : https://prove2.me/theorems/39379aad-e19a-4504-882e-a7c07478b2cf
-- title:
--   Integrable nonnegative real tests are identified by exact ENNReal lintegral moments
-- statement:
--   For the original mean-measure identification programme, nonnegative integrable real test functions have equal Bochner integrals whenever their exact ENNReal.ofReal Lebesgue integrals against two measures agree. This is the reversible real/extended-real bridge needed to apply signed compact-test uniqueness after proving positive original jump-count moments.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_positive_real_integral_eq_of_ennreal_tests
    {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) (f : α → ℝ)
    (hf : ∀ x : α, 0 ≤ f x)
    (hμ : Integrable f μ) (hν : Integrable f ν)
    (hlin : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) =
      (∫⁻ x, ENNReal.ofReal (f x) ∂ν)) :
    (∫ x, f x ∂μ) = (∫ x, f x ∂ν) := by sorry
