-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_stopped_Taylor_physical_square_energy_complement_band_tendsto_zero
-- name    : AvramDividend.Classical.avram_wave6_02_actual_discounted_stopped_Taylor_physical_square_energy_complement_band_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:51:45.521177+00:00
-- url     : https://prove2.me/theorems/afa5a126-e2d3-44c9-b023-b7dd0f0a50b8
-- title:
--   Actual discounted stopped Taylor physical predictable square-energy tail vanishes under every increasing exhaustive marked-band sequence
-- statement:
--   For the actual original spectrally negative Lévy path and controlled discounted inclusive ruin-stopped C2 Taylor kernel GW, the predictable product square-energy GW² has vanishing L1 absolute integral outside increasing exhaustive measurable marked bands. Uses separately Proved original product Integrable GW²; no assumption of a finite raw Lévy small-jump first moment.
-- source:
--   Proved 18c4c0c0 actual physical square integrability of GW and pinned tendsto_lintegral_norm_of_dominated_convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_ruin_stopped_Taylor_rightcont_product_MemLp
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_stopped_Taylor_rightcont_physical_product_L1_energy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_ruin_stopped_Taylor_predictable_square_integrable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_02_actual_discounted_stopped_Taylor_physical_square_energy_complement_band_tendsto_zero
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
      ∀ (B : ℕ → Set (((ℝ≥0 × Ω) × ℝ)))
        (hB : ∀ n, MeasurableSet (B n))
        (hBmono : Monotone B)
        (hBcover : (⋃ n, B n) = Set.univ),
      Tendsto (fun n =>
        ∫⁻ p, ENNReal.ofReal
          (|((B n)ᶜ).indicator (fun p => GW p ^ 2) p|)
          ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
        atTop (𝓝 0)) := by sorry
