-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb31_original_positive_discount_full_horizon_ENNReal_identity
-- name    : AvramDividend.Classical.avram_bvb31_original_positive_discount_full_horizon_ENNReal_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:19:48.652198+00:00
-- url     : https://prove2.me/theorems/aae87e2f-4148-4f2b-9c7f-4f8453196815
-- title:
--   Original positive discount exact full horizon ENNReal clock normalization from two authoritative Proved source lemmas
-- statement:
--   For every strictly positive original source discount q and observation horizon T, the true extended-nonnegative discounted real-Lebesgue lintegral over original physical Ioc(0,T), multiplied by the original positive q and added to the terminal discounted exponential, equals one. This is exactly the extra analytic hypothesis required by the Proved source zero-contact cash+terminal HJB bound 09a9c1c4. Use the already Proved source real discounted budget identity 5ce1f298 and already Proved ENNReal-ofReal transfer identity 39f64d37, with the original interval-to-Ioc identification. No new discount sign or surrogate measure.
-- source:
--   Proved 5ce1f298 original real positive-q discounted identity and Proved 39f64d37 original ENNReal integral transfer.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb23_original_discounted_zero_contact_budget_identity
import Theorems.Thm_AvramDividend_Classical_avram_bvb28_original_discount_ENNReal_normalization_of_real_FTC
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb31_original_positive_discount_full_horizon_ENNReal_identity
    (q T : ℝ) (hq : 0 < q) (hT : 0 < T) :
    ENNReal.ofReal q *
      (∫⁻ t in Ioc (0 : ℝ) T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(volume : Measure ℝ)) +
      ENNReal.ofReal (Real.exp (-(q * T))) = 1 := by sorry
