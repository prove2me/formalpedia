-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_tilted_of_laplace_cumulative_identification_full_support
-- name    : AvramDividend.Classical.positive_tilted_of_laplace_cumulative_identification_full_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T23:15:33.601106+00:00
-- url     : https://prove2.me/theorems/02d57749-a8af-4f53-acd7-a747bc751dc0
-- title:
--   Positive tilted scale function from cumulative Laplace identification without a zero atom
-- statement:
--   If the exponential normalisation of W is continuous and nonnegative on (0,infinity), and its Laplace transform agrees on a half-plane with the cumulative distribution of a positive measure with finite cumulative mass and positive cumulative mass at every positive reserve, then W is strictly positive and its exponential normalisation is nondecreasing. No atom at zero is assumed, unlike the proved bounded-variation version. This generic terminal bridge supports the zero-at-origin unbounded-variation Lévy scale function via a future Wiener-Hopf or ladder-potential representation.
-- source:
--   Generalises Proved AvramDividend.Classical.positive_tilted_of_laplace_cumulative_identification (UUID 94f2b582-a787-435e-9640-3bb790dafee6) and uses Proved Laplace uniqueness and cumulative right-continuity with new positive_tilted_of_exponential_cumulative_measure_full_support.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped ENNReal

theorem AvramDividend.Classical.positive_tilted_of_laplace_cumulative_identification_full_support
    (β : Measure ℝ) (φ b : ℝ) (hφ : 0 < φ)
    (hfin : ∀ x : ℝ, β (Iic x) ≠ ⊤)
    (hmass : ∀ x : ℝ, 0 < x → 0 < β (Iic x))
    (W : ℝ → ℝ)
    (htiltcont : ContinuousOn
      (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0))
    (htiltnonneg : ∀ x : ℝ, 0 < x →
      0 ≤ Real.exp (-φ * x) * W x)
    (hlap : ∀ θ : ℝ, b < θ →
      IntegrableOn
        (fun x : ℝ => Real.exp (-θ * x) *
          (Real.exp (-φ * x) * W x)) (Ioi 0) ∧
      IntegrableOn
        (fun x : ℝ => Real.exp (-θ * x) * (β (Iic x)).toReal) (Ioi 0) ∧
      ∫ x in Ioi (0 : ℝ),
          Real.exp (-θ * x) * (Real.exp (-φ * x) * W x) =
        ∫ x in Ioi (0 : ℝ),
          Real.exp (-θ * x) * (β (Iic x)).toReal) :
    (∀ x : ℝ, 0 < x → 0 < W x) ∧
      MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by sorry
