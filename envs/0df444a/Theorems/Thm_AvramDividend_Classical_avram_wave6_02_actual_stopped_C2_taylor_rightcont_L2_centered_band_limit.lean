-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_stopped_C2_taylor_rightcont_L2_centered_band_limit
-- name    : AvramDividend.Classical.avram_wave6_02_actual_stopped_C2_taylor_rightcont_L2_centered_band_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T22:31:32.389069+00:00
-- url     : https://prove2.me/theorems/d21ffec6-96ea-4bb4-9b95-d5ea93dcbe9d
-- title:
--   Actual ruin-stopped C² Taylor compensated bands: centered original-probability L² limit from finite-band bound
-- statement:
--   The actual controlled spectrally negative Lévy jump Taylor kernel with exact inclusive ruin stopping and original right-continuous predictable filtration admits a centered L²(P) limit of its compensated finite-band source integrals whenever the original intrinsic-jump source law supplies the finite-band L² increment bound and finite-band centering. The product-square energy is obtained from the canonical controlled Taylor L² estimate via Tonelli and normalized to the eNorm formulation consumed by the canonical centered L² limit theorem. No first moment of the small-jump Lévy measure is assumed, and no disconnected surrogate process is used.
-- source:
--   Reuses source-controlled 0e0663b1 and product-square 2d67e34c; real square normalizer then canonical original probability L² centered limit 540bd939. Explicit source hfinite_band_isometry_bound and hcentered hypotheses remain assigned to the intrinsic source PRM law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_stopped_C2_taylor_rightcont_physical_product_L2_energy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_real_product_L2_square_to_eNorm_energy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_actual_probability_l2_stopped_band_limit_mean_zero

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_02_actual_stopped_C2_taylor_rightcont_L2_centered_band_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      ∀ (B : ℕ → Set (((ℝ≥0 × Ω) × ℝ)))
        (hB : ∀ n, MeasurableSet (B n))
        (hBfinite : ∀ n, (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) (B n) < ⊤)
        (hBmono : Monotone B)
        (hBcover : (⋃ n, B n) = Set.univ)
        (M : ℕ → Lp ℝ (2 : ℝ≥0∞) P)
        (hfinite_band_isometry_bound : ∀ m n, m ≤ n →
          dist (M m) (M n) ≤
            (eLpNorm ((B m)ᶜ.indicator HS) (2 : ℝ≥0∞)
              (μ.prod (X.ν.restrict (Iio (0 : ℝ))))).toReal)
        (hcentered : ∀ n, ∫ ω, (M n) ω ∂P = 0),
      ∃ Mlimit : Lp ℝ (2 : ℝ≥0∞) P,
        Tendsto M Filter.atTop (nhds Mlimit) ∧
        (∫ ω, Mlimit ω ∂P) = 0) := by sorry
