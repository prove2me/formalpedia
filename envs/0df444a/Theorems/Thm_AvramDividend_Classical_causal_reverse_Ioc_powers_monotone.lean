-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_reverse_Ioc_powers_monotone
-- name    : AvramDividend.Classical.causal_reverse_Ioc_powers_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:49:03.729974+00:00
-- url     : https://prove2.me/theorems/dae0a666-0196-428b-be4b-23376a5b6e7e
-- title:
--   Monotonicity of reverse-oriented causal convolution powers
-- statement:
--   Every continuous causal convolution power of a nonnegative monotone kernel is monotone even when its recurrence uses f(x-s)U_n(s), the orientation produced by exponential factorisation. Use the accepted unrestricted real commutativity theorem to rewrite to f(s)U_n(x-s), then invoke the accepted monotonicity bridge. Enables the undamped positive-discount Neumann series to be monotone.
-- source:
--   Proved causal_Ioc_convolution_comm_all_real and causal_Ioc_convolution_powers_monotone_of_positive_kernel.

import Theorems.Thm_AvramDividend_Classical_causal_Ioc_convolution_powers_monotone_of_positive_kernel
import Theorems.Thm_AvramDividend_Classical_causal_Ioc_convolution_comm_all_real
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_reverse_Ioc_powers_monotone
    (f : ℝ → ℝ) (U : ℕ → ℝ → ℝ)
    (hfzero : ∀ x : ℝ, x ≤ 0 → f x = 0)
    (hfcont : Continuous f)
    (hfmono : Monotone f)
    (hfpos : ∀ x : ℝ, 0 ≤ f x)
    (hUcont : ∀ n : ℕ, Continuous (U n))
    (hU0 : U 0 = f)
    (hUrec : ∀ n : ℕ, ∀ x : ℝ,
      U (n + 1) x =
        ∫ s in Ioc (0 : ℝ) x, f (x - s) * U n s ∂volume) :
    ∀ n : ℕ, Monotone (U n) := by sorry
