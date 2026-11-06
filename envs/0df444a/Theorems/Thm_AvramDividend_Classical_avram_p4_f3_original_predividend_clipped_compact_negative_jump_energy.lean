-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_predividend_clipped_compact_negative_jump_energy
-- name    : AvramDividend.Classical.avram_p4_f3_original_predividend_clipped_compact_negative_jump_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:21:40.755195+00:00
-- url     : https://prove2.me/theorems/310fbc08-f045-4a41-aef3-56040616ceb8
-- title:
--   Original actual pre-dividend left-limit clipped compact reserve has finite physical jump intensity energy
-- statement:
--   For the same original X, dividend process D and pre-dividend reserve left limit x+X.X-rightLimit D, clip its reserve into a specified strict positive compact interval using the actual reserve's current value when inside. Its literal negative-jump coefficient square is integrable over the original negative Lévy ν and any finite time-probability localisation measure. This removes the abstract reserve-section assumption from the earlier P4-F3 energy theorem while retaining the physical original process. Clipping is explicit and does not assert exhaustion of the full ruin-clock, predictability, or a stochastic identity.
-- source:
--   Explicitly defines the actual original pre-payment left-limit reserve x+X.X-rightLimit D, clips it to δ on the complement of its positive compact interval, and proves this clipped physical reserve remains in the compact band. The public P4-F3 original finite-base ν-square energy theorem then applies to the same Ω, X, P and ν. No stochastic mean-zero property is assumed.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_compact_negative_jump_finite_base_quadratic_energy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_predividend_clipped_compact_negative_jump_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C)
    (μ : Measure (ℝ≥0 × Ω)) (hμ : μ Set.univ < ⊤) :
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ K then y else δ
    (∫⁻ p, ∫⁻ z in Iio (0 : ℝ),
      ENNReal.ofReal ((w (U p + z) - w (U p)) ^ 2) ∂X.ν ∂μ) < ⊤ := by sorry
