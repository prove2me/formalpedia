-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_past_full_band_future_borel_cross_condExp_zero
-- name    : AvramDividend.Classical.avram_p4_f3_original_past_full_band_future_borel_cross_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:49:20.525089+00:00
-- url     : https://prove2.me/theorems/9c10168f-69e7-4b10-a625-107bb86dd4b6
-- title:
--   Actual original past negative-band count is conditionally orthogonal to a later Borel jump cell
-- statement:
--   For the actual original Lévy process, the centred physical negative-band jump count on (0,s] is conditionally orthogonal to every later compensated physical marked Borel count on (s,t] with a strictly negative mark band, even for different bands and without assumed independent copies. The past count itself is proved measurable in the original filtration and L², and the future conditional-zero theorem accepts this unbounded past predictor.
-- source:
--   Formal bridge from proved original past marked count raw filtration measurability 41007669, original full-band centred L2 963870c8, and independently proved P4-F3 unbounded weighted negative Borel cell conditional mean 5f565ecd (required as Proved/public). The result supplies the exact actual-source off-time covariance step used by finite-grid orthogonality; no assumption of adaptedness, independent counts or replacement law.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_past_count_raw_measurable_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_unbounded_predictable_negative_cell_condExp_auto
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_past_full_band_future_borel_cross_condExp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (n m : ℕ)
    (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
    (hB : MeasurableSet B) (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : B ⊆ Iic (-(1 / ((m : ℝ) + 1)))) :
    let Jpast : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 s ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
    let Jfuture : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
    let rp : ℝ :=
      ((s : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    let rf : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
    P[(fun ω => ((Jpast ω).toReal - rp) *
      ((Jfuture ω).toReal - rf)) | 𝓕 s] =ᵐ[P] 0 := by sorry
