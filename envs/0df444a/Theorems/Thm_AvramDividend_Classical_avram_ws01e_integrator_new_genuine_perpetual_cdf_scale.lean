-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_integrator_new_genuine_perpetual_cdf_scale
-- name    : AvramDividend.Classical.avram_ws01e_integrator_new_genuine_perpetual_cdf_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:03:38.93599+00:00
-- url     : https://prove2.me/theorems/44e9b6c5-0c6f-4905-8208-e16a2658ef9b
-- title:
--   Genuine perpetual Esscher survival CDF equals positive-root normalised q-scale function
-- statement:
--   For any actual spectrally negative Levy process, q>0 and positive Esscher root phi satisfying psi(phi)=q, every source-defined q-scale W has a genuine perpetual Esscher weighted non-ruin survival probability law nu and positive m. The law's exact CDF over all real capital is the infimum of true finite-horizon weighted survival expectations, and at every positive capital x this is exactly m exp(-phi*x) Wq(x). This uses the accepted canonical Wiener-Hopf scalar, accepted support/CDF construction, and Proved positive-root supported-infimum Laplace-to-scale uniqueness. It assumes no path-space tilted probability or stochastic killed exit premise.
-- source:
--   Accepted canonical scalar 07c7d8b4-44ae-416c-8ef4-c205398f5876, supported genuine probability f370f2ab-18c8-417f-8739-ff5d31dd12aa, proved analytic CDF identification 337381bd-873a-4ffa-a5cf-072cae6066c8 (candidate 17973), pinned Mathlib Measure.ext_of_Iic and actual Lévy scale definition. Postclosure positive-interior strengthening prepared solely by Workstream 1E integrator, distinct from independently owned stopped harmonicity be9dc931.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_esscher_positive_root_perpetual_probability_support_laplace
import Theorems.Thm_AvramDividend_Classical_esscher_positive_root_perpetual_infimum_wiener_hopf_scalar
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_integrator_new_supported_infimum_laplace_identifies_scale

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_integrator_new_genuine_perpetual_cdf_scale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ (ν : Measure ℝ) (m : ℝ),
      IsProbabilityMeasure ν ∧ 0 < m ∧
      (∀ x : ℝ, ν (Iic x) =
        (⨅ t : ℝ≥0, ENNReal.ofReal
          (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
            (fun ω => Real.exp (φ * X.X t ω -
              (t : ℝ) * laplaceExponent X.c X.σ X.ν φ)) ω ∂P))) ∧
      (∀ x : ℝ, 0 < x → ν (Iic x) =
        ENNReal.ofReal (m * Real.exp (-(φ * x)) * W x)) := by sorry
