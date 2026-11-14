-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB303_nonnegative_real_cell_integral_to_lintegral
-- name    : AvramDividend.Classical.avram_gbB303_nonnegative_real_cell_integral_to_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:27:30.73163+00:00
-- url     : https://prove2.me/theorems/b2f539b0-29c9-49cb-aaa4-bfd36366c3f6
-- title:
--   A nonnegative physical-cell real integral bound transfers to its extended-real time lintegral
-- statement:
--   Given an integrable nonnegative real physical-time density on a finite interval with nonnegative width, an ordinary real interval-integral upper bound K implies an extended-nonnegative-real Lebesgue integral bound of its ofReal image by ofReal K. This is the essential conversion between B293 ordinary Gaussian inverse square-root integrals and the original probability-by-time occupation mass in B299.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB303_nonnegative_real_cell_integral_to_lintegral
    (s δ K : ℝ) (hδ : 0 ≤ δ)
    (f : ℝ → ℝ)
    (hf : IntegrableOn f (Set.Ioc s (s + δ)) volume)
    (hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc s (s + δ))] f)
    (hbound : (∫ t in s..(s + δ), f t) ≤ K) :
    (∫⁻ t in Set.Ioc s (s + δ), ENNReal.ofReal (f t) ∂volume) ≤
      ENNReal.ofReal K := by sorry
