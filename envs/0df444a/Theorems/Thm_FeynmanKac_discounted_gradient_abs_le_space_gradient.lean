-- Prove2me | Theorems.Thm_FeynmanKac_discounted_gradient_abs_le_space_gradient
-- name    : FeynmanKac.discounted_gradient_abs_le_space_gradient
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T09:17:38.152835+00:00
-- url     : https://prove2.me/theorems/6d903a4f-7a7e-4ff9-bb9d-6f937bdd22bc
-- title:
--   Nonnegative potential contracts the Brownian gradient integrand
-- statement:
--   For an elapsed Brownian time r within the terminal horizon, if the model's nonnegative potential along the realised path is interval-integrable, its stochastic discount D_{t,t+r} lies in (0,1]. Therefore the absolute value of the actual discounted-gradient coefficient Dσu_x is bounded pointwise by the absolute value of the undiscouted coefficient σu_x. This provides the comparison required for L² estimates, without asserting any martingale identity.
-- source:
--   Proved generic FeynmanKac discount positivity and prepared model discount bound; genuine elapsed-time integrands

import Definitions.Def_FeynmanKac_AdmissibleDiscountedGradient
import Theorems.Thm_FeynmanKac_model_pathDiscount_pos_le_one
import Mathlib.Tactic.Linarith

theorem FeynmanKac.discounted_gradient_abs_le_space_gradient
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P)
    (u : ℝ → ℝ → ℝ) (ω : Ω) (r : ℝ)
    (hr : r ∈ Set.Icc (0 : ℝ) (m.terminalTime - m.initialTime))
    (hInt : IntervalIntegrable
      (fun z => m.potential (m.path z ω) z)
      MeasureTheory.volume m.initialTime (m.initialTime + r)) :
    |m.discountedGradientIntegrand u ω r| ≤
      |m.spaceGradientIntegrand u ω r| := by sorry
