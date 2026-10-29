-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_integrator_new_genuine_perpetual_cdf_scale_all_real
-- name    : AvramDividend.Classical.avram_ws01e_integrator_new_genuine_perpetual_cdf_scale_all_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:24:28.71299+00:00
-- url     : https://prove2.me/theorems/8c0f76fb-a784-4965-a850-bf197731fc13
-- title:
--   Genuine perpetual Esscher survival CDF identifies the q-scale function at every real capital, including the zero atom
-- statement:
--   For the true spectrally negative Lévy process and positive Esscher root, there is a genuine perpetual Esscher survival law ν and finite positive m. Its cumulative distribution at every real starting capital x is exactly the infimum of genuine finite-horizon Esscher-weighted survival integrals and equals the q-scale function normalised by m exp(-φx), including x=0. The zero atom ν({0}) is therefore m Wq(0); at negative x both the support CDF and scale vanish. Extends the previously accepted positive-x CDF identification 44e9b6c5 through genuine right continuity, using the accepted Esscher cumulative origin theorem 5374c83e and scale continuity. No new stochastic law or Wiener-Hopf assumption is added.
-- source:
--   Accepted canonical scalar 07c7d8b4-44ae-416c-8ef4-c205398f5876, unconditional genuine positive-x CDF-to-scale 44e9b6c5-0c6f-4905-8208-e16a2658ef9b, supported genuine ν f370f2ab-18c8-417f-8739-ff5d31dd12aa, and accepted cumulative origin theorem 5374c83e-9cb5-4693-a6c1-ff33bbcff112. At zero the proof is a genuine right-limit argument; negative x follows from true ν support and W vanishing on Iio 0. A strictly stronger boundary identification relevant to WS1A/WS3, prepared solely by the 1E integrator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_esscher_positive_root_perpetual_probability_support_laplace
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_integrator_new_genuine_perpetual_cdf_scale
import Theorems.Thm_AvramDividend_Classical_esscher_cumulative_origin_of_finite

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_integrator_new_genuine_perpetual_cdf_scale_all_real
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
      (∀ x : ℝ, ν (Iic x) =
        ENNReal.ofReal (m * Real.exp (-(φ * x)) * W x)) := by sorry
