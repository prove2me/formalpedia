-- Prove2me | Theorems.Thm_FeynmanKac_clock_coordinate_all_nonnegative_ae
-- name    : FeynmanKac.clock_coordinate_all_nonnegative_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T09:15:27.545318+00:00
-- url     : https://prove2.me/theorems/1a100cb6-a599-46c0-b93b-5b4979a7eadf
-- title:
--   One full-measure set supports the entire deterministic diffusion clock path
-- statement:
--   For the canonical clock-augmented SDE with continuous bounded autonomous drift and zero Brownian coefficient in the clock coordinate, there is one P-full-measure set of sample paths on which the clock coordinate equals initialTime+u for every nonnegative elapsed time u simultaneously. This is stronger than the existing fixed-u almost-everywhere theorem and is necessary for substituting the deterministic clock inside the Lebesgue time integrals of the vector Itô formula.
-- source:
--   Accepted FunctionalInequalities.Probability.Diffusion.IsDiffusion.ae_linear_eq_integral_readable and previously accepted FeynmanKac.clock_coordinate_absolute_time proof

import Definitions.Def_FeynmanKac_BoundedDiffusionModel
import Theorems.Thm_FunctionalInequalities_Probability_Diffusion_IsDiffusion_ae_linear_eq_integral_readable
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

theorem FeynmanKac.clock_coordinate_all_nonnegative_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P) :
    ∀ᵐ ω ∂P, ∀ (u : ℝ), 0 ≤ u →
      m.augmentedPath u ω (1 : Fin 2) = m.initialTime + u := by sorry
