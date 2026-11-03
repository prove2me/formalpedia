-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_Taylor_physical_signed_compensator_cutoff_error_le_L1_tail
-- name    : AvramDividend.Classical.avram_wave6_02_actual_discounted_Taylor_physical_signed_compensator_cutoff_error_le_L1_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T08:02:12.498833+00:00
-- url     : https://prove2.me/theorems/54750f64-e5b8-45f7-bb52-00a1f70cbf30
-- title:
--   Actual original physical signed predictable Taylor compensator cutoff error bounded by excluded absolute L1 energy
-- statement:
--   For the original controlled discounted inclusive ruin-stopped C² Taylor kernel GW and arbitrary measurable predictable-product marked cutoff A, the absolute difference of the physical ν-compensator integrals of 1_A GW and GW is bounded by the physical absolute L1 tail ∫|1_(Aᶜ)GW|. The true full original product L1 integrability is used explicitly, not inferred from L2 on infinite Lévy intensity and not from a finite raw first small-jump moment.
-- source:
--   Accepted actual original product Integrable GW; pinned Set.indicator_compl_add_self, integral_add, and norm_integral_le_integral_norm.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_ruin_stopped_Taylor_rightcont_product_MemLp
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_stopped_Taylor_rightcont_physical_product_L1_energy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_ruin_stopped_Taylor_predictable_product_Integrable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_02_actual_discounted_Taylor_physical_signed_compensator_cutoff_error_le_L1_tail
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
      ∀ (A : Set (((ℝ≥0 × Ω) × ℝ))) (hA : MeasurableSet A),
      |(∫ p, A.indicator GW p
          ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) -
        (∫ p, GW p
          ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ)))))| ≤
      (∫ p, |(Aᶜ).indicator GW p|
        ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) ) := by sorry
