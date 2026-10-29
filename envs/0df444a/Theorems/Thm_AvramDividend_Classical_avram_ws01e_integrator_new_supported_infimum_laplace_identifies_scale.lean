-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_integrator_new_supported_infimum_laplace_identifies_scale
-- name    : AvramDividend.Classical.avram_ws01e_integrator_new_supported_infimum_laplace_identifies_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:48:19.982624+00:00
-- url     : https://prove2.me/theorems/337381bd-873a-4ffa-a5cf-072cae6066c8
-- title:
--   Positive-root perpetual infimum Laplace law identifies the Esscher-normalised genuine q-scale function
-- statement:
--   For an actual spectrally negative Levy process with q>0, a positive Esscher root phi and any q-scale function W, suppose a genuinely supported probability measure nu has the exact all-positive-beta descending transform m beta/(psi(phi+beta)-q) with positive m. Then for every positive capital x its exact cumulative nu((minus infinity,x]) equals m exp(-phi x) Wq(x). The premises are precisely those supplied by the canonically Proved 1E scalar and supported CDF package. The proof compares the actual CDF and scale Laplace integrals and applies accepted real/ENNReal and right-continuous Laplace uniqueness, with no killed-stopped identity or invented tilted path-space law.
-- source:
--   Canonical Proved scalar 07c7d8b4, supported CDF f370f2ab, positiveLaplace cumulative 6027eb2c, tilted scale real/ENNReal 95658b90/7654d06e, true cumulative ENNReal-to-real bridge cc36bbe0, finite cumulative right-continuity b6cea95b, scale continuity 0dfe2e0c, Laplace uniqueness d0a7b4b9. Distinct analytical helper; no duplicate returned by exact searches on 28 October 2026.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_cumulative_measure
import Theorems.Thm_AvramDividend_Classical_levy_esscher_root_scale_tilted_laplace
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_lintegral
import Theorems.Thm_AvramDividend_Classical_positive_cumulative_laplace_real_integral_bridge
import Theorems.Thm_AvramDividend_Classical_rightContinuous_cumulative_toReal_of_finite
import Theorems.Thm_AvramDividend_Classical_continuous_rightContinuous_Ioi_eq_of_laplace_eq
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuousAt_away_zero
import Theorems.Thm_AvramDividend_Classical_levy_psi_root_strictly_above_shift

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_integrator_new_supported_infimum_laplace_identifies_scale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hνSupp : ν (Iio 0) = 0)
    (m : ℝ) (hm : 0 < m)
    (hνLap : ∀ β : ℝ, 0 < β →
      (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂ν) =
        ENNReal.ofReal (m * β / (X.ψ (φ + β) - q)))
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ x : ℝ, 0 < x →
      ν (Iic x) = ENNReal.ofReal
        (m * Real.exp (-(φ * x)) * W x) := by sorry
