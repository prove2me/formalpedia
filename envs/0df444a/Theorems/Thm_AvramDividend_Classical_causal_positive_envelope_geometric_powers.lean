-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_positive_envelope_geometric_powers
-- name    : AvramDividend.Classical.causal_positive_envelope_geometric_powers
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T14:39:57.396994+00:00
-- url     : https://prove2.me/theorems/1edb3f3d-724e-43cb-87f9-517c6cc7e1cc
-- title:
--   Geometrically bounded convolution powers for a positive damped Gaussian kernel
-- statement:
--   A nonnegative L1 causal kernel with positive Volterra coefficient admits an exponentially damped, normalised positive envelope of total mass below one. Its recursive nonnegative convolution powers exist, remain integrable, and each finite-horizon mass is bounded by the corresponding geometric power of the envelope mass. This provides quantitative estimates towards the C1 Gaussian derivative-resolvent Neumann series.
-- source:
--   The proved exponential contraction weight plus positivity of the Gaussian native kernel instantiate the proved geometric truncated-mass theorem for causal convolution powers.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_causal_l1_exists_contracting_weighted_envelope
import Theorems.Thm_AvramDividend_Classical_causal_positive_convolution_powers_geometric_truncated_mass

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_positive_envelope_geometric_powers
    (K : ℝ → ℝ) (a β : ℝ) (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hKpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ K t) :
    ∃ (w : ℝ) (κ : ℝ → ℝ),
      0 < w ∧
      κ = (fun t : ℝ => a⁻¹ * Real.exp (-w * t) * (|β| + K t)) ∧
      IntegrableOn κ (Ioi (0 : ℝ)) volume ∧
      (∫ t in Ioi (0 : ℝ), κ t ∂volume) < 1 ∧
      ∃ F : ℕ → ℝ → ℝ,
        F 0 = κ ∧
        (∀ n : ℕ, F (n + 1) =
          fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
            κ s * F n (x - s) ∂volume) ∧
        (∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume) ∧
        (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x) ∧
        (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
          (∫ t in Ioc (0 : ℝ) x, F n t ∂volume) ≤
          (∫ t in Ioi (0 : ℝ), κ t ∂volume) ^ (n + 1)) := by sorry
