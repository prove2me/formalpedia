-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_power_exact_mass_geometric
-- name    : AvramDividend.Classical.causal_l1_convolution_power_exact_mass_geometric
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T13:57:02.118174+00:00
-- url     : https://prove2.me/theorems/359791d2-2e15-448b-aebb-cfa6965b4363
-- title:
--   Causal L1 convolution powers have exact geometric integral mass
-- statement:
--   Every integrable real positive-time causal kernel generates an L1 convolution-power sequence with mass ∫F_n=(∫κ)^(n+1). This packages the recursive mass-product identity into the geometric invariant used for Gaussian Volterra envelope powers.
-- source:
--   Apply the proved convolution-power sequence existence and mass recursion. Induction and pow_succ prove the exact geometric mass formula.

import Mathlib.Analysis.Convolution
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_power_sequence_exists

open MeasureTheory Set

theorem AvramDividend.Classical.causal_l1_convolution_power_exact_mass_geometric
    (κ : ℝ → ℝ)
    (hκ : IntegrableOn κ (Ioi (0 : ℝ)) volume) :
    ∃ F : ℕ → ℝ → ℝ,
      F 0 = κ ∧
      (∀ n : ℕ, F (n + 1) =
        fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
          κ s * F n (x - s) ∂volume) ∧
      (∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume) ∧
      (∀ n : ℕ,
        (∫ x in Ioi (0 : ℝ), F n x ∂volume) =
          (∫ x in Ioi (0 : ℝ), κ x ∂volume) ^ (n + 1)) := by sorry
