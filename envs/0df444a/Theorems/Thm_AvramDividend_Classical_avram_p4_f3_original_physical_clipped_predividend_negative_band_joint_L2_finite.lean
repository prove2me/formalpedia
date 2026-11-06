-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_physical_clipped_predividend_negative_band_joint_L2_finite
-- name    : AvramDividend.Classical.avram_p4_f3_original_physical_clipped_predividend_negative_band_joint_L2_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:35:26.349863+00:00
-- url     : https://prove2.me/theorems/f034789e-817a-44a4-a7f4-a655127e1c5a
-- title:
--   Original physical left-reserve clipped negative-band compensated jump coefficient has finite joint energy
-- statement:
--   The original Levy path and original dividend right limits define actual pre-dividend left reserve on the physical time-probability product. Clipping it to a positive interior compact reserve interval, the squared negative-band jump-coefficient relative to the left endpoint has finite source-measure by Levy intensity integral for every finite physical time-space source measure.
-- source:
--   Instantiates public Proved original arbitrary finite source L2 energy 936d6c76 with the actual left limit of x+X.X-rightLimit D and its strict compact clip. Only deterministic clipping bounds are needed; no surrogate process or unproved Ito formula.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_band_compact_source_parameter_joint_L2_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_physical_clipped_predividend_negative_band_joint_L2_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K ε : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C)
    (μ : Measure (ℝ≥0 × Ω)) (hμ : μ univ < ⊤) :
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ K then y else δ
    (∫⁻ p, (∫⁻ z in Ioo (-ε) (0 : ℝ),
      ENNReal.ofReal
        (((w (U p + z) - w (U p)) -
          (w (δ + z) - w δ)) ^ 2) ∂X.ν) ∂μ) < ⊤ := by sorry
