-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_damped_antitone_envelope_quadratic
-- name    : AvramDividend.Classical.causal_damped_antitone_envelope_quadratic
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T15:42:04.343288+00:00
-- url     : https://prove2.me/theorems/02f81a7b-8d25-4400-8d66-a482179cc418
-- title:
--   Gaussian damped positive envelope with quadratic-geometric pointwise powers
-- statement:
--   For a positive nonincreasing continuous L1 causal Gaussian-type kernel, an exponential damping weight makes the positive envelope contracting; all its nonnegative convolution powers remain L1, obey geometric mass bounds and satisfy uniform positive-time quadratic-geometric pointwise decay. The witnesses retain the actual convolution recursion and all quantitative constants for Neumann-series regularity.
-- source:
--   Combine the proved damped-envelope geometric L1 powers with the antitone Ioc pointwise transfer, preserving all power recursions and mass controls; use positive-time kernel continuity and monotonicity to derive the weighted assumptions. This is the positive majorant used to dominate signed Neumann kernels in gaussian_esscher_C1_derivative_resolvent_of_positive_sigma.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_causal_positive_envelope_geometric_powers
import Theorems.Thm_AvramDividend_Classical_causal_weighted_antitone_kernel
import Theorems.Thm_AvramDividend_Classical_causal_weighted_kernel_continuous_positive
import Theorems.Thm_AvramDividend_Classical_causal_antitone_Ioc_powers_quadratic

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_damped_antitone_envelope_quadratic
    (K : ℝ → ℝ) (a β : ℝ) (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hKpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ K t)
    (hKanti : AntitoneOn K (Ioi (0 : ℝ)))
    (hKcont : ContinuousOn K (Ioi (0 : ℝ))) :
    ∃ (w : ℝ) (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ),
      0 < w ∧
      κ = (fun t : ℝ => a⁻¹ * Real.exp (-w * t) * (|β| + K t)) ∧
      IntegrableOn κ (Ioi (0 : ℝ)) volume ∧
      0 ≤ (∫ t in Ioi (0 : ℝ), κ t ∂volume) ∧
      (∫ t in Ioi (0 : ℝ), κ t ∂volume) < 1 ∧
      F 0 = κ ∧
      (∀ n : ℕ, F (n + 1) =
        fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
          κ s * F n (x - s) ∂volume) ∧
      (∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
        (∫ s in Ioc (0 : ℝ) x, F n s ∂volume) ≤
          (∫ s in Ioi (0 : ℝ), κ s ∂volume) ^ (n + 1)) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 < x →
        F n x ≤ ((n + 1 : ℝ) ^ 2 *
          (∫ s in Ioi (0 : ℝ), κ s ∂volume) ^ (n + 1)) / x) := by sorry
