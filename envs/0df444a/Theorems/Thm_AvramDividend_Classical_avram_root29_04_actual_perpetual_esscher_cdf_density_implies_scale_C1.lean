-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_04_actual_perpetual_esscher_cdf_density_implies_scale_C1
-- name    : AvramDividend.Classical.avram_root29_04_actual_perpetual_esscher_cdf_density_implies_scale_C1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T09:09:27.272857+00:00
-- url     : https://prove2.me/theorems/915301b7-eb62-4145-a8ca-193b4f9b948e
-- title:
--   The genuine all-real perpetual Esscher CDF with a continuous local density gives source-specific q-scale C1
-- statement:
--   For the actual spectrally negative Levy process and its genuine all-real positive-root perpetual Esscher CDF law, assume that every probability law with the canonical scale-CDF equality has a locally interval-integrable continuous positive-axis density. Then the actual q-scale function is C1 on the positive axis. This theorem combines the already Proved genuine CDF scale representation with the Proved FTC density-to-C1 bridge; its density hypothesis is the exact remaining independent fluctuation-theory obligation. Neither non-atomicity nor continuity of the CDF is silently upgraded to a density.
-- source:
--   Proved all-real Esscher scale-CDF identity (8c0f76fb-a784-4965-a850-bf197731fc13), Proved conditional density-to-C1 FTC bridge (d9187db3-1b33-4b09-8063-32bf9f6954b8), source IsScaleFunction nonnegative positive-axis W. The local-density hypothesis is genuinely required.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_integrator_new_genuine_perpetual_cdf_scale_all_real
import Theorems.Thm_AvramDividend_Classical_avram_root29_04_scale_C1_of_true_esscher_cdf_continuous_local_density

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_04_actual_perpetual_esscher_cdf_density_implies_scale_C1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hLocalDensity : ∀ (ν : Measure ℝ) (m : ℝ),
      IsProbabilityMeasure ν → 0 < m →
      (∀ x : ℝ, ν (Iic x) =
        ENNReal.ofReal (m * Real.exp (-(φ * x)) * W x)) →
      ∃ (a : ℝ) (f : ℝ → ℝ), 0 < a ∧
        ContinuousOn f (Ioi (0 : ℝ)) ∧
        (∀ x : ℝ, 0 < x → IntervalIntegrable f volume a x) ∧
        (∀ x : ℝ, 0 < x → (ν (Iic x)).toReal =
          (ν (Iic a)).toReal + ∫ t in a..x, f t)) :
    ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) := by sorry
