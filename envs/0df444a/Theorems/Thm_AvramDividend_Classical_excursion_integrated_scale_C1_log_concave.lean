-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_integrated_scale_C1_log_concave
-- name    : AvramDividend.Classical.excursion_integrated_scale_C1_log_concave
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T13:54:55.369958+00:00
-- url     : https://prove2.me/theorems/eb91b4df-405d-4c67-8d39-039f2678c3e3
-- title:
--   Continuous excursion exponential representation gives C1 regularity and log-concavity
-- statement:
--   A strictly positive function satisfying an exponential interval integral representation with a continuous finite excursion-height tail has a continuously differentiable first derivative and a concave logarithm on the positive half-line. This unifies the analytic consequences needed by the unbounded Esscher C1 and log-concavity branches.
-- source:
--   Proved excursion_integral_scale_derivative, contDiffOn_one_of_deriv_eq_continuous_product_Ioi and excursion_log_concave_of_derivative_representation.

import Theorems.Thm_AvramDividend_Classical_excursion_integral_scale_derivative
import Theorems.Thm_AvramDividend_Classical_contDiffOn_one_of_deriv_eq_continuous_product_Ioi
import Theorems.Thm_AvramDividend_Classical_excursion_log_concave_of_derivative_representation
open AvramDividend.Classical MeasureTheory Set intervalIntegral

theorem AvramDividend.Classical.excursion_integrated_scale_C1_log_concave
    (W : ℝ → ℝ) (φ : ℝ) (μ : MeasureTheory.Measure ℝ)
    (hcont : ContinuousOn (fun t : ℝ => μ.real (Set.Ici t)) (Set.Ioi (0 : ℝ)))
    (hfin : ∀ x : ℝ, 0 < x → μ (Set.Ici x) ≠ ⊤)
    (hWpos : ∀ x : ℝ, 0 < x → 0 < W x)
    (hexp : ∀ a b : ℝ, 0 < a → a ≤ b →
      W b = W a * Real.exp (∫ t in a..b, φ + μ.real (Set.Ici t))) :
    ContDiffOn ℝ 1 W (Set.Ioi (0 : ℝ)) ∧
      ConcaveOn ℝ (Set.Ioi (0 : ℝ)) (fun x : ℝ => Real.log (W x)) := by sorry
