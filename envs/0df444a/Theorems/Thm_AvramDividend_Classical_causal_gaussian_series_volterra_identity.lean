-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_gaussian_series_volterra_identity
-- name    : AvramDividend.Classical.causal_gaussian_series_volterra_identity
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-24T22:26:25.261057+00:00
-- url     : https://prove2.me/theorems/12cb7290-55e1-4bce-a17f-2015bdab2943
-- title:
--   Summable Gaussian signed convolution powers satisfy the derivative Volterra equation
-- statement:
--   For a Gaussian signed Neumann convolution-power sequence that admits geometric bounds and measurable corrections, the pointwise series g solves a g(x) plus the causal Gaussian Volterra convolution equal to one. This is the key equation needed to promote the C1 series candidate into a scale-function second-derivative proof.
-- source:
--   Combine the canonically Proved Gaussian head, tail, nonpositive and global recurrence, reflected-kernel integrability and geometric Neumann dominated-convergence identity. This converts the constructed signed Gaussian series to the exact RHS=1 derivative-resolvent equation, the missing analytic step in gaussian_esscher_C1_derivative_resolvent_of_positive_sigma.

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

theorem AvramDividend.Classical.causal_gaussian_series_volterra_identity
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
