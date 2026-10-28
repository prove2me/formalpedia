-- Prove2me | Theorems.Thm_FeynmanKac_augmented_coefficients_eq_time_dependent_ae
-- name    : FeynmanKac.augmented_coefficients_eq_time_dependent_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T09:11:03.422985+00:00
-- url     : https://prove2.me/theorems/d3405d5f-7b56-42f7-9175-f310a73121f0
-- title:
--   Augmented vector diffusion coefficients equal the original time-dependent coefficients
-- statement:
--   For the actual clock-augmented diffusion, the spatial drift and Brownian volatility coefficient along its augmented state agree almost surely at each nonnegative elapsed Brownian time r with μ(X_{t+r},t+r) and σ(X_{t+r},t+r). Use the already proved deterministic clock-coordinate identity Y¹_r=t+r, the model's coefficient identities, and the definition X_{t+r}=Y⁰_r. This is the concrete coefficient-reduction bridge needed to specialise the vector Itô theorem to the one-dimensional time-dependent Feynman–Kac formula.
-- source:
--   Accepted FeynmanKac.clock_coordinate_absolute_time; published BoundedDiffusionModel coefficient-field identities

import Definitions.Def_FeynmanKac_BoundedDiffusionModel
import Theorems.Thm_FeynmanKac_clock_coordinate_absolute_time

theorem FeynmanKac.augmented_coefficients_eq_time_dependent_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P)
    (r : ℝ) (hr : 0 ≤ r) :
    (fun ω => m.augmentedDrift (m.augmentedPath r ω) (0 : Fin 2)) =ᵐ[P]
      (fun ω => m.drift (m.path (m.initialTime + r) ω) (m.initialTime + r)) ∧
    (fun ω => m.augmentedVolatility (m.augmentedPath r ω) 0 (0 : Fin 2)) =ᵐ[P]
      (fun ω => m.volatility (m.path (m.initialTime + r) ω) (m.initialTime + r)) := by sorry
