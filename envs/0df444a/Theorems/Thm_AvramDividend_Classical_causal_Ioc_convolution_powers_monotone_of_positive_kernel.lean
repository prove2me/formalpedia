-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_Ioc_convolution_powers_monotone_of_positive_kernel
-- name    : AvramDividend.Classical.causal_Ioc_convolution_powers_monotone_of_positive_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:27:19.640027+00:00
-- url     : https://prove2.me/theorems/3f7dac13-35f4-468f-9608-0517b03870f0
-- title:
--   Monotonicity of continuous causal Ioc convolution powers of a positive monotone kernel
-- statement:
--   A nonnegative globally nondecreasing causal kernel has nondecreasing Ioc convolution powers, provided their continuity is known. Causal Ioc-to-real recurrence and compact-support integrability discharge the global convolution-power monotonicity lemma. This is the monotonicity needed for the undamped positive-discount scale renewal series.
-- source:
--   Proved causal_Ioc_convolution_powers_full_real_recursion; causal_continuous_product_integrable_full; full_convolution_powers_monotone_of_nonnegative_kernel.

import Theorems.Thm_AvramDividend_Classical_causal_Ioc_convolution_powers_full_real_recursion
import Theorems.Thm_AvramDividend_Classical_causal_continuous_product_integrable_full
import Theorems.Thm_AvramDividend_Classical_full_convolution_powers_monotone_of_nonnegative_kernel
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_Ioc_convolution_powers_monotone_of_positive_kernel
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ)
    (hκzero : ∀ x : ℝ, x ≤ 0 → κ x = 0)
    (hκcont : Continuous κ)
    (hκmono : Monotone κ)
    (hκpos : ∀ x : ℝ, 0 ≤ κ x)
    (hFcont : ∀ n : ℕ, Continuous (F n))
    (hF0 : F 0 = κ)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y in Ioc (0 : ℝ) x,
        κ y * F n (x - y) ∂volume) :
    ∀ n : ℕ, Monotone (F n) := by sorry
