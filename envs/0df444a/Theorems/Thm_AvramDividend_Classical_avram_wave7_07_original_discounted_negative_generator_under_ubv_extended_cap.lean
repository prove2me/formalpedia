-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_discounted_negative_generator_under_ubv_extended_cap
-- name    : AvramDividend.Classical.avram_wave7_07_original_discounted_negative_generator_under_ubv_extended_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:46:29.871012+00:00
-- url     : https://prove2.me/theorems/b36e4265-4e1b-4476-9869-c21361739a2a
-- title:
--   Original negative-jump discounted stopped generator with W7-08 extended-real cap C² hypothesis
-- statement:
--   On the original SpectrallyNegativeLevy process and right-continuous predictable filtration, transfer the automatically discounted stopped negative-jump compensating product integral to the negative generator using W7-08's exact extended-real C² smoothness condition and any finite real localisation bound R lying strictly below C.
-- source:
--   W7-07 bridge to the unbounded-variation W7-08 canonical stopped Itô–Meyer inequality; unchanged original jump process, discount, ruin time and generator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_discounted_stopped_negative_taylor_product_eq_generator_auto_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_ubv_extended_cap_local_C2_restrict

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_original_discounted_negative_generator_under_ubv_extended_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (R u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < R)
    (hRcap : ENNReal.ofReal R < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
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
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    (∫ r : ((ℝ≥0 × Ω) × ℝ),
      Real.exp (-(q * (r.1.1 : ℝ))) * HS r
      ∂(letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
        μ.prod (X.ν.restrict (Iio (0 : ℝ))))) =
    (∫ p : ℝ≥0 × Ω,
      Real.exp (-(q * (p.1 : ℝ))) *
        (∫ z in Iio (0 : ℝ), G (p,z) ∂X.ν) ∂μ) := by sorry
