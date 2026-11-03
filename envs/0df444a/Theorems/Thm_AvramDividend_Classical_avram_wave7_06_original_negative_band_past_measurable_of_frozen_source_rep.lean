-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_past_measurable_of_frozen_source_rep
-- name    : AvramDividend.Classical.avram_wave7_06_original_negative_band_past_measurable_of_frozen_source_rep
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T22:04:30.47226+00:00
-- url     : https://prove2.me/theorems/735b8fa1-7b98-498e-ad33-5c95b9e57888
-- title:
--   Original negative-band past void event measurable from an explicit stopped-source path counter
-- statement:
--   For the true intrinsic marked count of the original Lévy field X on Ω, suppose the count over the past window (0,T] in a fixed separated negative band admits one measurable functional of the original path frozen at T. Then the original past-void event is measurable in the raw filtration 𝓕 T. The proof uses adaptedness at min(v,T), monotonicity of 𝓕, and coordinate-product measurability; no count law or Poisson assumption. The frozen-prefix representation is explicitly an additional premise that future work must establish.
-- source:
--   W7-06 supporting raw-filtration hPast needed by the original negative-band void semigroup d94c1f15-8caa-469a-a43c-84758c62ae81. In particular hFrozen is not silently inferred from the global path extractor and must be discharged by a source-specific prefix-locality argument.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_negative_band_past_measurable_of_frozen_source_rep
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω = ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (T : ℝ≥0) (n : ℕ)
    (F : (ℝ≥0 → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (hFrozen : ∀ ω : Ω,
      NX ω (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) =
        F (fun v : ℝ≥0 => X.X (min v T) ω)) :
    MeasurableSet[𝓕 T]
      {ω : Ω | NX ω (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} := by sorry
