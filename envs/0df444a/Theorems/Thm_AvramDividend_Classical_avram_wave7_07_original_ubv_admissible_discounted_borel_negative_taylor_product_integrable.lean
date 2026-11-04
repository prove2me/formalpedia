-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_ubv_admissible_discounted_borel_negative_taylor_product_integrable
-- name    : AvramDividend.Classical.avram_wave7_07_original_ubv_admissible_discounted_borel_negative_taylor_product_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T06:59:05.515776+00:00
-- url     : https://prove2.me/theorems/d992c221-2246-4ea2-a60f-6494871fef95
-- title:
--   UBV admissible discounted stopped C2 Taylor Bochner L1 over original negative Borel marks
-- statement:
--   The exact original controlled left-limit reserve X.X minus D, inclusive ruin stopping and C² negative-jump Taylor remainder are Bochner-integrable on the finite original predictable clock times X.ν restricted to negative marks, thinned by an arbitrary negative measurable Borel set B and weighted by exp(-qt), q≥0. The canonical UBV extended-real cap localises to finite C² cutoff and hD.1.1 is the original strategy. Original signed predictable product-integrable theorem and measurable-discount lemma establish the result.
-- source:
--   W7-07 source-specific actual Lévy stopped discounted Taylor L1 import for W7-08.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_signed_predictable_negative_taylor_product_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_ubv_positive_band_finite_C2_cutoff_exists
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_predictable_time_exponential_discount_measurable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_original_ubv_admissible_discounted_borel_negative_taylor_product_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : ENNReal.ofReal v < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (B : Set ℝ) (hBm : MeasurableSet B)
    (hBneg : B ⊆ Iio (0 : ℝ))
    (q : ℝ) (hq : 0 ≤ q) :
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
    let S : Set ((ℝ≥0 × Ω) × ℝ) := {r | r.2 ∈ B}
    Integrable (fun r : ((ℝ≥0 × Ω) × ℝ) =>
      (S.indicator (fun r => Real.exp (-(q * (r.1.1 : ℝ))) * HS r)) r) (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
      μ.prod (X.ν.restrict (Iio (0 : ℝ)))) := by sorry
