-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_power_sequence_exists
-- name    : AvramDividend.Classical.causal_l1_convolution_power_sequence_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T12:30:36.45272+00:00
-- url     : https://prove2.me/theorems/0458ffeb-6ad8-4a29-892c-444f8165ec90
-- title:
--   Recursive causal L1 convolution powers exist with exact multiplicative mass
-- statement:
--   Every real L1 kernel on strictly positive time generates a recursively defined sequence F0=κ, F_(n+1)=κ*F_n of real causal convolution powers. All powers remain L1 on positive time and their total masses satisfy the exact multiplicative recursion. This supplies the analytic mass invariant needed for polynomial-geometric bounds on positive envelope powers.
-- source:
--   Induct on Nat.rec using the published positive causal convolution Laplace-integrability theorem at θ=0 and newly proved causal L1 convolution mass-product theorem.

import Mathlib.Analysis.Convolution
import Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_laplace_integrable
import Theorems.Thm_AvramDividend_Classical_causal_l1_positive_convolution_mass_product

open MeasureTheory Set

theorem AvramDividend.Classical.causal_l1_convolution_power_sequence_exists
    (κ : ℝ → ℝ)
    (hκ : IntegrableOn κ (Ioi (0 : ℝ)) volume) :
    ∃ F : ℕ → ℝ → ℝ,
      F 0 = κ ∧
      (∀ n : ℕ, F (n + 1) =
        fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
          κ s * F n (x - s) ∂volume) ∧
      (∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume) ∧
      (∀ n : ℕ,
        (∫ x in Ioi (0 : ℝ), F (n + 1) x ∂volume) =
        (∫ x in Ioi (0 : ℝ), κ x ∂volume) *
          (∫ x in Ioi (0 : ℝ), F n x ∂volume)) := by sorry
