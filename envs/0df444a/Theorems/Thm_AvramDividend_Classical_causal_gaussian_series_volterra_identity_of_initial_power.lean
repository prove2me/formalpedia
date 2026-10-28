-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_gaussian_series_volterra_identity_of_initial_power
-- name    : AvramDividend.Classical.causal_gaussian_series_volterra_identity_of_initial_power
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T22:37:42.260381+00:00
-- url     : https://prove2.me/theorems/b819f0ad-6ced-4f54-8e0f-c332662bc4e9
-- title:
--   Signed Gaussian Neumann series with initial kernel power solves the derivative Volterra equation
-- statement:
--   A Gaussian signed Neumann convolution-power sequence starting at its specified kernel and having geometric bounds satisfies the exact derivative Volterra equation. The first-power identity provides the mathematically necessary head recurrence.
-- source:
--   The initial signed Neumann convolution power must satisfy P0=k. With this exact necessary hypothesis, combine the canonically Proved Gaussian head, tail, nonpositive and global recurrence, reflected-kernel integrability and geometric dominated-convergence theorem. The prior published series theorem omitting P0=k is mathematically insufficient and remains Open.

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_neumann_gaussian_head_step
import Theorems.Thm_AvramDividend_Classical_causal_neumann_gaussian_tail_step
import Theorems.Thm_AvramDividend_Classical_causal_neumann_gaussian_nonpositive_zero
import Theorems.Thm_AvramDividend_Classical_causal_neumann_head_tail_global_step
import Theorems.Thm_AvramDividend_Classical_causal_gaussian_reflected_full_kernel_integrable
import Theorems.Thm_AvramDividend_Classical_causal_geometric_neumann_resolvent
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_gaussian_series_volterra_identity_of_initial_power
    (a w β ρ : ℝ) (K k : ℝ → ℝ)
    (P Q : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (ha : 0 < a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hk : k = fun t : ℝ =>
      if 0 < t then -(a⁻¹ * Real.exp (-w * t) * (β + K t)) else 0)
    (hkL1 : IntegrableOn k (Ioi (0 : ℝ)) volume)
    (hPL1 : ∀ n : ℕ, IntegrableOn (P n) (Ioi (0 : ℝ)) volume)
    (hPrec : ∀ n : ℕ, P (n + 1) =
      fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, k s * P n (x - s) ∂volume)
    (hP0 : P 0 = k)
    (hQ0 : Q 0 = fun _ : ℝ => 1 / a)
    (hQsucc : ∀ n : ℕ, Q (n + 1) = fun x : ℝ =>
      (1 / a) * (∫ t in Ioc (0 : ℝ) x,
        Real.exp (w * t) * P n t ∂volume))
    (hMeas : ∀ x : ℝ, ∀ i : ℕ, AEStronglyMeasurable
      (Q i) (volume.restrict (Ioc (0 : ℝ) x)))
    (hGeom : ∀ x : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, ∀ s ∈ Ioc (0 : ℝ) x, ‖Q n s‖ ≤ C * ρ ^ n)
    (hPoint : ∀ x : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, ‖Q n x‖ ≤ C * ρ ^ n)
    (hg : ∀ x : ℝ, g x = ∑' n : ℕ, Q n x) :
    ∀ x : ℝ, a * g x +
      (∫ s in Ioc (0 : ℝ) x,
        (β + K (x - s)) * g s ∂volume) = 1 := by sorry
