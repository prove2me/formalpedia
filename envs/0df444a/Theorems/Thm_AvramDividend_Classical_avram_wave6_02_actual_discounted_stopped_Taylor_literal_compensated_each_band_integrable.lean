-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_stopped_Taylor_literal_compensated_each_band_integrable
-- name    : AvramDividend.Classical.avram_wave6_02_actual_discounted_stopped_Taylor_literal_compensated_each_band_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:22:47.943413+00:00
-- url     : https://prove2.me/theorems/1d014854-7950-4c75-9529-e9a1deaceefe
-- title:
--   Actual original-source literal discounted ruin-stopped compensated Taylor jump band is P-integrable, every n
-- statement:
--   Every original intrinsic X-jump count finite-band compensated source Taylor term, with inclusive ruin stopping, discount, actual predictable product and original ν compensator, is genuinely Integrable on original probability P. Transfer Lp2(P) integrability of the source image to literal pathwise jump-count difference through hSource n; never assume finite first raw small-jump moment.
-- source:
--   Pinned MeasureTheory.MemLp.integrable for 1≤2 on probability P; MeasureTheory.Integrable.congr and the original hSource n AE equality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_ruin_stopped_Taylor_rightcont_product_MemLp
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_02_actual_discounted_stopped_Taylor_literal_compensated_each_band_integrable
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
        Integrable (fun ω =>
          (∫ p, (B n).indicator GW ((p.1, ω), p.2) ∂(NX ω)) -
          ∫ t, ∫ z, (B n).indicator GW ((t, ω), z) ∂X.ν ∂clock) P) := by sorry
