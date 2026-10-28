-- Prove2me | Theorems.Thm_FeynmanKac_discounted_gradient_ito_integral_martingale
-- name    : FeynmanKac.discounted_gradient_ito_integral_martingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T08:37:40.203199+00:00
-- url     : https://prove2.me/theorems/d0852845-445e-4cd3-9c9e-bcdc8da9355e
-- title:
--   Genuine discounted-gradient Brownian integral is a true martingale
-- statement:
--   For a genuine clock-augmented Brownian model, the completed Itô integral of its discounted spatial-gradient coefficient is a true martingale in the Brownian elapsed-time variable r. The coefficient is evaluated at absolute time t+r, with the integral evaluated at r; its independently verified admissibility witness supplies joint measurability, progressive measurability and finite quadratic energy. This theorem is a specialisation of the accepted general Brownian integral martingale theorem, and assumes no Feynman–Kac representation or reward martingale.
-- source:
--   LevyStochCalc/Brownian/ItoL2CompletionMaster and FeynmanKac_AdmissibleDiscountedGradient

import Definitions.Def_FeynmanKac_AdmissibleDiscountedGradient

theorem FeynmanKac.discounted_gradient_ito_integral_martingale
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P)
    (u : ℝ → ℝ → ℝ)
    (h : m.AdmissibleDiscountedGradient u) :
    MeasureTheory.Martingale
      (fun r ω =>
        m.discountedGradientItoIntegral u h (m.initialTime + r) ω)
      m.filtration P := by sorry
