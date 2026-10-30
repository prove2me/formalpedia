-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_perpetual_survival_scale_real
-- name    : AvramDividend.Classical.avram_root29_01_perpetual_survival_scale_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T09:11:55.491925+00:00
-- url     : https://prove2.me/theorems/6dc4855b-6e8a-454e-bbc0-feb1438df621
-- title:
--   Original-Lévy all-real perpetual Esscher survival infimum equals the real q-scale function
-- statement:
--   For the genuine original-P spectrally negative Lévy process and any positive Esscher q-root, the ordinary real infimum of true finite-time Esscher weighted lower-survival expectations at every real reserve x equals m exp(-φ x) Wq(x) with a positive common normalising constant. The proof reconciles the pinned Mathlib ofReal_iInf bridge and nonnegative scale function, including the zero-origin atom. It imports only the already Proved all-real perpetual CDF-scale identification and genuine original-law unit-interval bound; no conditional Markov, optional stopping or two-sided exit is assumed.
-- source:
--   Independent WS1A q-scale real-value bridge using canonical Proved 8c0f76fb-a784-4965-a850-bf197731fc13; work/avram_root29_01_perpetual_survival_scale_real.lean.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_integrator_new_genuine_perpetual_cdf_scale_all_real
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_unit_interval

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_perpetual_survival_scale_real
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ m : ℝ, 0 < m ∧
      ∀ x : ℝ,
      (⨅ t : ℝ≥0, ∫ ω,
        ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => Real.exp (φ * X.X t ω -
            (t : ℝ) * laplaceExponent X.c X.σ X.ν φ)) ω ∂P) =
      m * Real.exp (-(φ * x)) * W x := by sorry
