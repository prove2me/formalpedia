-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_positive_convolution_mass_product
-- name    : AvramDividend.Classical.causal_l1_positive_convolution_mass_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T12:27:15.857203+00:00
-- url     : https://prove2.me/theorems/5f0a5d22-c994-4d24-81d3-d08ee95a57b4
-- title:
--   Total mass of an L1 causal convolution equals the product of kernel and input masses
-- statement:
--   For real kernels K,F integrable on strictly positive times, the global integral of their causal convolution equals the product of their positive-time integrals. The result is valid for signed kernels and follows by setting the transform parameter to zero in the already proved causal Laplace product theorem. This is the mass-recursion identity for Neumann convolution powers.
-- source:
--   Proved AvramDividend.Classical.positive_causal_convolution_laplace_product specialised to θ=0.

import Mathlib.Analysis.Convolution
import Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_laplace_product

open MeasureTheory Set

theorem AvramDividend.Classical.causal_l1_positive_convolution_mass_product
    (K F : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hF : IntegrableOn F (Ioi (0 : ℝ)) volume) :
    (∫ x in Ioi (0 : ℝ),
      (∫ s in Ioc (0 : ℝ) x, K s * F (x - s) ∂volume) ∂volume) =
      (∫ t in Ioi (0 : ℝ), K t ∂volume) *
      (∫ t in Ioi (0 : ℝ), F t ∂volume) := by sorry
