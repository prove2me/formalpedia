-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_stopped_Taylor_exists_finite_physical_predictable_band_with_small_L2_tail
-- name    : AvramDividend.Classical.avram_wave6_02_actual_discounted_stopped_Taylor_exists_finite_physical_predictable_band_with_small_L2_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:57:43.002372+00:00
-- url     : https://prove2.me/theorems/368dd6e4-b8f4-49ce-9154-15bd41d167a3
-- title:
--   Actual ruin-stopped discounted Taylor source admits arbitrarily accurate finite-measure original predictable marked L2 localisations
-- statement:
--   For actual original spectrally negative Lévy X, adapted dividends D, finite discount horizon and inclusive ruin-stopped C² Taylor GW, any nonzero ε admits a measurable right-continuous predictable-product marked set A of finite μ×ν_- measure such that the excluded physical GW L2 energy norm is below ε. Genuine original source and exact stopping, no surrogate Poisson space or finite raw first small-jump moment.
-- source:
--   Pinned Mathlib MemLp.exists_eLpNorm_indicator_compl_lt on original product MemLp2 of actual discounted stopped GW.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_ruin_stopped_Taylor_rightcont_product_MemLp
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_02_actual_discounted_stopped_Taylor_exists_finite_physical_predictable_band_with_small_L2_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
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
      ∀ (ε : ℝ≥0∞) (hε : ε ≠ 0),
      ∃ A : Set (((ℝ≥0 × Ω) × ℝ)),
        MeasurableSet A ∧
        (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) A < ⊤ ∧
        eLpNorm (Aᶜ.indicator GW) (2 : ℝ≥0∞)
          (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) < ε) := by sorry
