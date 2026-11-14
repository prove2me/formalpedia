-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb28_original_discount_ENNReal_normalization_of_real_FTC
-- name    : AvramDividend.Classical.avram_bvb28_original_discount_ENNReal_normalization_of_real_FTC
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:18:54.548759+00:00
-- url     : https://prove2.me/theorems/39f64d37-37a7-42e1-af70-a904437d1291
-- title:
--   Original positive-discount finite-horizon real FTC normalisation transfers exactly to full ENNReal HJB discount-clock identity
-- statement:
--   Under the exact real finite-horizon exponential discount identity, transfer the physical discounted Ioc time integral into the original extended-nonnegative Bochner-independent lintegral. For strictly positive discount q and observation horizon T, the real integral of exp(-qt) is nonnegative and integrable; pinned Mathlib identifies its ofReal with the original physical ENNReal lintegral. The exact nonnegative ofReal addition and multiplication preserve q and the terminal exponential. The result is precisely the additional discount-clock hypothesis in the authoritative original zero-contact compensated cash budget theorem 09a9c1c4.
-- source:
--   Pinned Mathlib ofReal_integral_eq_lintegral_ofReal, Continuous.integrableOn_Ioc, ENNReal.ofReal_add/mul. Original cash bound 09a9c1c4.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb28_original_discount_ENNReal_normalization_of_real_FTC
    (q T : ℝ) (hq : 0 < q) (hT : 0 < T)
    (hReal : q * (∫ t in Ioc (0 : ℝ) T,
        Real.exp (-(q * t)) ∂(volume : Measure ℝ)) +
        Real.exp (-(q * T)) = 1) :
    ENNReal.ofReal q *
      (∫⁻ t in Ioc (0 : ℝ) T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(volume : Measure ℝ)) +
      ENNReal.ofReal (Real.exp (-(q * T))) = 1 := by sorry
