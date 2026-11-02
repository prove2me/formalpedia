-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_stopped_Taylor_intrinsic_source_L2_limit_integrable_zero_mean
-- name    : AvramDividend.Classical.avram_wave6_02_actual_stopped_Taylor_intrinsic_source_L2_limit_integrable_zero_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T22:49:22.791863+00:00
-- url     : https://prove2.me/theorems/864f1949-36c8-4ccd-8b8c-b08b1e1e94cb
-- title:
--   Original intrinsic stopped Taylor compensated L² limit is genuinely L¹(P)-integrable and centered
-- statement:
--   For the actual spectrally negative Lévy source X, original adapted dividend D and inclusive ruin-stopped C² Taylor H_S, the original centered L²(P) finite-band intrinsic compensated limit is additionally P-integrable, not merely an extended integral equal to zero. Reuses the Proved source-faithful rightCont isometry-to-tail limit and finite probability's L²-to-L¹ embedding. Explicit source hIso/hZero/hSource and finite-band assumptions remain precisely those of the original jump-source theorem.
-- source:
--   Canonical accepted source-exact L² limit b41f13ce, pinned Mathlib Lp.memLp, MemLp.integrable under IsProbabilityMeasure P.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_stopped_C2_taylor_intrinsic_source_isometry_L2_limit
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_02_actual_stopped_Taylor_intrinsic_source_L2_limit_integrable_zero_mean
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
      let hML : MemLp HS (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) :=
        avram_wave6_02_actual_stopped_C2_taylor_rightcont_physical_product_MemLp
          X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv μ hμ;
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
          (I ((hML.indicator (hB n)).toLp ((B n).indicator HS)) : Ω → ℝ)
            =ᵐ[P] fun ω =>
            (∫ p, (B n).indicator HS ((p.1, ω), p.2) ∂(NX ω)) -
              ∫ t, ∫ z, (B n).indicator HS ((t, ω), z) ∂X.ν ∂clock),
      ∃ Llimit : Lp ℝ (2 : ℝ≥0∞) P,
        Tendsto (fun n => I ((hML.indicator (hB n)).toLp
          ((B n).indicator HS))) Filter.atTop (nhds Llimit) ∧
        Integrable (fun ω => (Llimit ω : ℝ)) P ∧
        (∫ ω, Llimit ω ∂P) = 0 ∧
        (∀ m n, m ≤ n →
          dist (I ((hML.indicator (hB m)).toLp ((B m).indicator HS)))
            (I ((hML.indicator (hB n)).toLp ((B n).indicator HS))) ≤
            (eLpNorm ((B m)ᶜ.indicator HS) (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Iio (0 : ℝ))))).toReal) ∧
        (∀ n,
          (I ((hML.indicator (hB n)).toLp ((B n).indicator HS)) : Ω → ℝ)
            =ᵐ[P] fun ω =>
            (∫ p, (B n).indicator HS ((p.1, ω), p.2) ∂(NX ω)) -
              ∫ t, ∫ z, (B n).indicator HS ((t, ω), z) ∂X.ν ∂clock)) := by sorry
