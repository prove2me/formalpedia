-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_tilted_of_laplace_cumulative_identification
-- name    : AvramDividend.Classical.positive_tilted_of_laplace_cumulative_identification
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T00:00:50.231555+00:00
-- url     : https://prove2.me/theorems/94f2b582-a787-435e-9640-3bb790dafee6
-- title:
--   Tilted positivity and monotonicity from Laplace identification with a cumulative measure
-- statement:
--   If the exponentially tilted function exp(-φx)W(x) is continuous and nonnegative on (0,∞), and its Laplace transform agrees on a right half-line with the Laplace transform of the cumulative function x↦β((-∞,x]) for a locally finite measure β with positive mass at zero, then W is strictly positive on (0,∞) and the exponential tilt is nondecreasing there.
-- source:
--   Composition of the published right-continuous Laplace-uniqueness theorem with the accepted positive_tilted_of_exponential_cumulative_measure terminal bridge.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace AvramDividend.Classical

theorem positive_tilted_of_laplace_cumulative_identification
    (β : Measure ℝ) (φ b : ℝ) (hφ : 0 < φ)
    (hfin : ∀ x : ℝ, β (Iic x) ≠ ⊤)
    (hatom : 0 < β {0})
    (W : ℝ → ℝ)
    (htiltcont : ContinuousOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0))
    (htiltnonneg : ∀ x : ℝ, 0 < x → 0 ≤ Real.exp (-φ * x) * W x)
    (hlap : ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * (Real.exp (-φ * x) * W x)) (Ioi 0) ∧
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * (β (Iic x)).toReal) (Ioi 0) ∧
      ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * (Real.exp (-φ * x) * W x) =
        ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * (β (Iic x)).toReal) :
    (∀ x : ℝ, 0 < x → 0 < W x) ∧
      MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by
  sorry

end AvramDividend.Classical
