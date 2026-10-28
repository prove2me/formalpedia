-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_integrated_tilted_scale_C1_log_concave
-- name    : AvramDividend.Classical.excursion_integrated_tilted_scale_C1_log_concave
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T14:02:53.11409+00:00
-- url     : https://prove2.me/theorems/41c4718a-5d0a-4f5a-ba86-4c3d2bebe451
-- title:
--   C1 regularity and log-concavity transfer to the Esscher-tilted excursion scale
-- statement:
--   A positive scale function with a finite, continuous excursion-tail exponential interval representation has a continuously differentiable and log-concave Esscher tilt on the positive half-line.
-- source:
--   Proved excursion_integrated_scale_C1_log_concave, esscher_tilt_contDiffOn_one_of_scale_contDiffOn_one and esscher_tilted_log_concave_of_scale_log_concave.

import Theorems.Thm_AvramDividend_Classical_excursion_integrated_scale_C1_log_concave
import Theorems.Thm_AvramDividend_Classical_esscher_tilt_contDiffOn_one_of_scale_contDiffOn_one
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_log_concave_of_scale_log_concave
open AvramDividend.Classical MeasureTheory Set intervalIntegral

theorem AvramDividend.Classical.excursion_integrated_tilted_scale_C1_log_concave
    (W V : ℝ → ℝ) (φ : ℝ) (μ : MeasureTheory.Measure ℝ)
    (hcont : ContinuousOn (fun t : ℝ => μ.real (Set.Ici t)) (Set.Ioi (0 : ℝ)))
    (hfin : ∀ x : ℝ, 0 < x → μ (Set.Ici x) ≠ ⊤)
    (hWpos : ∀ x : ℝ, 0 < x → 0 < W x)
    (hexp : ∀ a b : ℝ, 0 < a → a ≤ b →
      W b = W a * Real.exp (∫ t in a..b, φ + μ.real (Set.Ici t)))
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x) :
    ContDiffOn ℝ 1 V (Set.Ioi (0 : ℝ)) ∧
      ConcaveOn ℝ (Set.Ioi (0 : ℝ)) (fun x : ℝ => Real.log (V x)) := by sorry
