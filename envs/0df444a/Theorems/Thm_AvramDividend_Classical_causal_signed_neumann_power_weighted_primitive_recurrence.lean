-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_signed_neumann_power_weighted_primitive_recurrence
-- name    : AvramDividend.Classical.causal_signed_neumann_power_weighted_primitive_recurrence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T20:46:05.34495+00:00
-- url     : https://prove2.me/theorems/714d6d01-59c8-4d53-ad8d-d030f6412337
-- title:
--   Weighted primitive recursion for every signed Neumann convolution power
-- statement:
--   Any integrable positive-time signed causal convolution power sequence has a precise exponentially weighted primitive recurrence on each finite positive time interval. This is the finite-step bridge between the C1 Gaussian Neumann-series construction and its resolvent identity.
-- source:
--   Apply the proved exponential local-L1 lemma separately to k and P n and the proved finite-horizon weighted convolution primitive step to the exact power recursion. Its conclusion provides the termwise recurrence needed to show the Gaussian C1 Neumann candidate solves the Volterra derivative resolvent equation.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_causal_exponential_positive_L1_integrableOn_Ioc
import Theorems.Thm_AvramDividend_Classical_causal_weighted_neumann_primitive_step_local_L1

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_signed_neumann_power_weighted_primitive_recurrence
    (k : ℝ → ℝ) (P : ℕ → ℝ → ℝ) (w : ℝ)
    (hkL1 : IntegrableOn k (Ioi (0 : ℝ)) volume)
    (hPL1 : ∀ n : ℕ, IntegrableOn (P n) (Ioi (0 : ℝ)) volume)
    (hPrec : ∀ n : ℕ, P (n + 1) =
      fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, k s * P n (x - s) ∂volume) :
    ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      (∫ t in Ioc (0 : ℝ) x, Real.exp (w * t) * P (n + 1) t ∂volume) =
      (∫ s in Ioc (0 : ℝ) x,
        (Real.exp (w * (x - s)) * k (x - s)) *
          (∫ t in Ioc (0 : ℝ) s,
            Real.exp (w * t) * P n t ∂volume) ∂volume) := by sorry
