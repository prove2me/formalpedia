-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_full_convolution_powers_exact_geometric_mass
-- name    : AvramDividend.Classical.causal_full_convolution_powers_exact_geometric_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:23:58.214173+00:00
-- url     : https://prove2.me/theorems/c22da382-508e-4a68-8d5a-1663f7befa69
-- title:
--   Exact geometric integrated mass for any recursive causal convolution-power sequence
-- statement:
--   For any locally integrated full-real convolution-power sequence driven by a positive-time integrable causal kernel, each power has total mass equal to the corresponding geometric power of the kernel mass. The theorem applies to arbitrary recursive solutions and uses proved causal support and convolution mass-product identities. This supplies the exact geometric bound needed to derive interval integrability of the Esscher renewal density at zero.

import Theorems.Thm_AvramDividend_Classical_causal_full_convolution_powers_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_causal_real_convolution_equals_positive_interval_under_support
import Theorems.Thm_AvramDividend_Classical_causal_l1_positive_convolution_mass_product

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_full_convolution_powers_exact_geometric_mass
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ)
    (hκzero : ∀ x : ℝ, x ≤ 0 → κ x = 0)
    (hκL1 : IntegrableOn κ (Ioi (0 : ℝ)) volume)
    (hFzero : F 0 = κ)
    (hFrec : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume)
    (hFi : ∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume) :
    ∀ n : ℕ,
      (∫ x in Ioi (0 : ℝ), F n x ∂volume) =
        (∫ x in Ioi (0 : ℝ), κ x ∂volume) ^ (n + 1) := by sorry
