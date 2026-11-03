-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_stopped_Taylor_real_compensated_band_L1_error_bound
-- name    : AvramDividend.Classical.avram_wave6_02_actual_discounted_stopped_Taylor_real_compensated_band_L1_error_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:56:40.189882+00:00
-- url     : https://prove2.me/theorems/83e60358-d9be-4350-ba42-7589e4669cb6
-- title:
--   Actual original-source ruin-stopped compensated finite-band Taylor L1 error has quantitative complementary predictable L2 energy bound
-- statement:
--   For actual original spectrally negative Levy path X and controlled dividends D, the literal compensated negative-jump C2 Taylor integral truncated to each measurable predictable band Bn has ordinary P-L1 absolute error against the canonical isometric full-integrand I(GW) bounded by the complement physical product L2 square energy. The original source representation hSource remains explicit; no detached Poisson space or finite first moment is assumed.
-- source:
--   The actual source hSource n identifies the literal compensated finite-band jump integral almost everywhere with I applied to the cutoff GW. Mathlib's Lp.coeFn_sub identifies the pointwise difference between this finite-band image and the full canonical image. Integral congruence transfers the ordinary absolute error, and the already-Proved actual source cutoff L1 error bound provides its complementary L2 energy estimate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_stopped_Taylor_source_cutoff_L1_error_bound
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_02_actual_discounted_stopped_Taylor_real_compensated_band_L1_error_bound
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
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let a : (ℝ≥0 × Ω) → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
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
    let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      let hML : MemLp GW (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) :=
        avram_wave6_02_actual_discounted_ruin_stopped_Taylor_rightcont_product_MemLp
          X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv q hq T μ hμ;
      ∀ (NX : Ω → Measure (ℝ≥0 × ℝ))
        (hNX : ∀ ω, NX ω =
          ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧
            X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
            (fun t : ℝ≥0 => (t, X.X t ω -
              Function.leftLim (fun s : ℝ≥0 => X.X s ω) t))))
        (B : ℕ → Set (((ℝ≥0 × Ω) × ℝ)))
        (hB : ∀ n, MeasurableSet (B n))
        (hBfinite : ∀ n, (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) (B n) < ⊤)
        (hBmono : Monotone B) (hBcover : (⋃ n, B n) = Set.univ)
        (I : Lp ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) →ₗ[ℝ] Lp ℝ (2 : ℝ≥0∞) P)
        (hIso : ∀ t, ‖I t‖ = ‖t‖)
        (hZero : ∀ t, ∫ ω, I t ω ∂P = 0)
        (clock : Measure ℝ≥0)
        (hSource : ∀ n,
          (I ((hML.indicator (hB n)).toLp ((B n).indicator GW)) : Ω → ℝ)
            =ᵐ[P] fun ω =>
            (∫ p, (B n).indicator GW ((p.1, ω), p.2) ∂(NX ω)) -
              ∫ t, ∫ z, (B n).indicator GW ((t, ω), z) ∂X.ν ∂clock),
      ∀ n,
        (∫ ω, |((∫ p, (B n).indicator GW ((p.1, ω), p.2) ∂(NX ω)) -
          ∫ t, ∫ z, (B n).indicator GW ((t, ω), z) ∂X.ν ∂clock) -
            (I (hML.toLp GW) ω : ℝ)| ∂P) ≤
          (eLpNorm ((B n)ᶜ.indicator GW) (2 : ℝ≥0∞)
            (μ.prod (X.ν.restrict (Iio (0 : ℝ))))).toReal) := by sorry
