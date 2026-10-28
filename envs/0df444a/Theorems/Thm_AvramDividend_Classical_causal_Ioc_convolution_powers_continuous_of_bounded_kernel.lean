-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_Ioc_convolution_powers_continuous_of_bounded_kernel
-- name    : AvramDividend.Classical.causal_Ioc_convolution_powers_continuous_of_bounded_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:24:44.771366+00:00
-- url     : https://prove2.me/theorems/3632303a-066e-4eb6-b34b-48454f53bb54
-- title:
--   Continuity of positive-interval renewal powers from a globally bounded causal kernel
-- statement:
--   A continuous globally bounded causal kernel and an Ioc-recursive integrable positive-time convolution sequence have continuous members on all real arguments. This combines already proved causal-support/full-convolution equivalence, full L1 integrability and bounded-kernel convolution continuity. It directly supplies continuity for the positive-discount Neumann construction.
-- source:
--   Proved causal_Ioc_convolution_powers_full_real_recursion; causal_positive_l1_global_integrable; causal_convolution_powers_continuous_of_bounded_kernel.

import Theorems.Thm_AvramDividend_Classical_causal_Ioc_convolution_powers_full_real_recursion
import Theorems.Thm_AvramDividend_Classical_causal_positive_l1_global_integrable
import Theorems.Thm_AvramDividend_Classical_causal_convolution_powers_continuous_of_bounded_kernel
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_Ioc_convolution_powers_continuous_of_bounded_kernel
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ)
    (hκzero : ∀ x : ℝ, x ≤ 0 → κ x = 0)
    (hκcont : Continuous κ)
    (hκbdd : BddAbove (Set.range fun x : ℝ => ‖κ x‖))
    (hF0 : F 0 = κ)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y in Ioc (0 : ℝ) x,
        κ y * F n (x - y) ∂volume)
    (hFi : ∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume) :
    ∀ n : ℕ, Continuous (F n) := by sorry
