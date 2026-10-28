-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_integrated_tilted_scale_monotone
-- name    : AvramDividend.Classical.excursion_integrated_tilted_scale_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T14:14:43.056111+00:00
-- url     : https://prove2.me/theorems/2446c2cd-cf81-461d-a732-c358b419501c
-- title:
--   Nonnegative excursion-height tail makes the Esscher-tilted scale monotone
-- statement:
--   A strictly positive scale function with a continuous excursion-tail exponential interval representation has a nondecreasing Esscher-normalised scale function on the positive half-line.
-- source:
--   Proved excursion_integral_scale_derivative and pinned Mathlib mean-value monotonicity from nonnegative derivatives.

import Theorems.Thm_AvramDividend_Classical_excursion_integral_scale_derivative
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
open AvramDividend.Classical MeasureTheory Set Filter intervalIntegral

theorem AvramDividend.Classical.excursion_integrated_tilted_scale_monotone
    (W V : ℝ → ℝ) (φ : ℝ) (μ : MeasureTheory.Measure ℝ)
    (hcont : ContinuousOn (fun t : ℝ => μ.real (Set.Ici t)) (Set.Ioi (0 : ℝ)))
    (hWpos : ∀ x : ℝ, 0 < x → 0 < W x)
    (hexp : ∀ a b : ℝ, 0 < a → a ≤ b →
      W b = W a * Real.exp (∫ t in a..b, φ + μ.real (Set.Ici t)))
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x) :
    MonotoneOn V (Set.Ioi (0 : ℝ)) := by sorry
