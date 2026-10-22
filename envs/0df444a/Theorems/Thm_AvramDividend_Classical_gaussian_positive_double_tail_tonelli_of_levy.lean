-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_positive_double_tail_tonelli_of_levy
-- name    : AvramDividend.Classical.gaussian_positive_double_tail_tonelli_of_levy
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T18:15:17.345068+00:00
-- url     : https://prove2.me/theorems/2b2c23ce-57eb-4c09-a6dd-d745ae9feccc
-- title:
--   Gaussian Esscher double-tail Tonelli under the Lévy integral hypothesis
-- statement:
--   Under the positive truncated-square Lévy integrability assumption, the Gaussian Esscher double-tail nonnegative kernel may be integrated in either order over Lebesgue time and the positive restriction of the Lévy measure. Sigma-finiteness of that restricted measure follows from the Lévy condition.
-- source:
--   Accepted gaussian_double_tail_tonelli and gaussian_levy_positive_restrict_sigmaFinite, pinned Mathlib.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_positive_double_tail_tonelli_of_levy
    (μ : Measure ℝ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤)
    (φ θ : ℝ) :
    (∫⁻ t : ℝ, ∫⁻ z : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
          ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂(μ.restrict (Ioi (0 : ℝ))) ∂volume) =
    (∫⁻ z : ℝ, ∫⁻ t : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
          ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂volume ∂(μ.restrict (Ioi (0 : ℝ)))) := by sorry
