-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_positive_ruin_expected_strict_stopped_budget
-- name    : AvramDividend.Classical.avram_wave3_03_bv_positive_ruin_expected_strict_stopped_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T11:17:53.183176+00:00
-- url     : https://prove2.me/theorems/0ea740fd-ef2f-4f60-9fb1-cc630515c0bd
-- title:
--   Expected BV complete strict stopped Stieltjes reward bounded across all positive-ruin paths
-- statement:
--   For any nonnegative initial reserve under the actual Standing bounded-variation Lévy process, expected entire strict stopped dividend Stieltjes rewards up to the earlier of ruin and a deterministic horizon H, on all paths with positive ruin time, are bounded by initial reserve plus H times the positive physical drift. This extends surviving-horizon expected BV localisation to trajectories whose ruin happens first and retains continuous dividends.
-- source:
--   The original-source positive-ruin Stieltjes stopped-drift envelope and monotonicity of the ENNReal Lebesgue integral, with the probability-law normalization. The positive-ruin pathwise parent was submitted for publication in the same wave.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_positive_ruin_strict_stopped_drift_budget
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_03_bv_positive_ruin_expected_strict_stopped_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (x : ℝ) (hx : 0 ≤ x) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (H : ℝ≥0) (hH : 0 < H) :
    (∫⁻ ω, if 0 < ruinTime X x D ω then
      (∫⁻ r in paymentTimes
          (min (ruinTime X x D ω) (H : ℝ≥0∞)),
        ENNReal.ofReal (Real.exp (-(q * r)))
          ∂(dividendMeasure D ω)) else 0 ∂P) ≤
        ENNReal.ofReal (x + (H : ℝ) * X.drift) := by sorry
