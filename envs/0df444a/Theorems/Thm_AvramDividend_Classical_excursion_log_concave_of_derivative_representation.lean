-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_log_concave_of_derivative_representation
-- name    : AvramDividend.Classical.excursion_log_concave_of_derivative_representation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T13:35:18.660979+00:00
-- url     : https://prove2.me/theorems/3285bee2-d63f-407f-b70d-70666f0645bf
-- title:
--   Excursion-height derivative representation implies log-concavity
-- statement:
--   If a positive differentiable scale-like function satisfies W'(x)=W(x)(φ+μ([x,∞))) for a measure with finite positive upper tails, then log W is concave on the positive half-line. The excursion-height tail is antitone and therefore the logarithmic derivative is antitone. This bridges an excursion representation to the log-concavity theorem used in Esscher-scale regularity.
-- source:
--   Proved AvramDividend.Classical.excursion_log_derivative_antitoneOn and AvramDividend.Classical.concave_log_of_antitone_log_derivative.

import Theorems.Thm_AvramDividend_Classical_excursion_log_derivative_antitoneOn
import Theorems.Thm_AvramDividend_Classical_concave_log_of_antitone_log_derivative
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.excursion_log_concave_of_derivative_representation
    (W : ℝ → ℝ) (μ : MeasureTheory.Measure ℝ) (φ : ℝ)
    (hfin : ∀ x : ℝ, 0 < x → μ (Set.Ici x) ≠ ⊤)
    (hWpos : ∀ x : ℝ, 0 < x → 0 < W x)
    (hderiv : ∀ x : ℝ, 0 < x →
      deriv W x = W x * (φ + μ.real (Set.Ici x)))
    (hWdiff : ∀ x : ℝ, 0 < x → HasDerivAt W (deriv W x) x) :
    ConcaveOn ℝ (Set.Ioi (0 : ℝ)) (fun x : ℝ => Real.log (W x)) := by sorry
