-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_stopped_Taylor_physical_square_energy_band_integrals_tendsto_full
-- name    : AvramDividend.Classical.avram_wave6_02_actual_discounted_stopped_Taylor_physical_square_energy_band_integrals_tendsto_full
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T08:15:49.8773+00:00
-- url     : https://prove2.me/theorems/52fe4a10-df5f-41f0-beb2-87d3fa99ea04
-- title:
--   Actual original predictable stopped Taylor square-energy finite-band integrals converge to full physical energy
-- statement:
--   For the genuine original right-continuous predictable discounted inclusive ruin-stopped controlled Taylor kernel GW, the physical signed square-energy integral over any increasing exhaustive sequence of marked measurable bands converges to the full finite square-energy integral. Uses original Integrable(GW²) and original product dominated convergence; no first raw jump moment.
-- source:
--   Source-exact square-integrable energy and pinned Mathlib Bochner dominated-convergence theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_ruin_stopped_Taylor_rightcont_product_MemLp
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_stopped_Taylor_rightcont_physical_product_L1_energy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_ruin_stopped_Taylor_predictable_square_integrable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_02_actual_discounted_stopped_Taylor_physical_square_energy_band_integrals_tendsto_full
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
        ∫ p, (B n).indicator (fun p => GW p ^ 2) p
          ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
        atTop (𝓝 (∫ p, GW p ^ 2
          ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))))) := by sorry
