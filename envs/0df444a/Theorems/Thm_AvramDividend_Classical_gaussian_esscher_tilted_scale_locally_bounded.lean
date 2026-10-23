-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_tilted_scale_locally_bounded
-- name    : AvramDividend.Classical.gaussian_esscher_tilted_scale_locally_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T11:09:42.388411+00:00
-- url     : https://prove2.me/theorems/93a63a62-bfef-4ce8-8b35-5acae0124e1c
-- title:
--   Local boundedness near zero for the Gaussian Esscher-tilted scale function
-- statement:
--   If the Gaussian coefficient is positive, the q-scale W satisfies W(0)=0. Since W is monotone, 0≤W(x)≤W(R) for 0<x≤R. A positive Esscher parameter has 0<exp(-phi*x)≤1, so |V(x)|≤W(R) on (0,R]. This gives the near-origin local boundedness needed by the integrated Gaussian Volterra equation without imposing the process standing moment condition.
-- source:
--   Proved scaleFunction_zero_origin_gaussian_without_standing and scaleFunction_monotone; elementary exponential bounds.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.gaussian_esscher_tilted_scale_locally_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x) :
    ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |V x| ≤ C := by sorry
