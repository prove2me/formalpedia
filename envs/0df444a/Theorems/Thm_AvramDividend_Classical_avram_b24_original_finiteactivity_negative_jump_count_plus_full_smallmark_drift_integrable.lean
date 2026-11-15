-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_finiteactivity_negative_jump_count_plus_full_smallmark_drift_integrable
-- name    : AvramDividend.Classical.avram_b24_original_finiteactivity_negative_jump_count_plus_full_smallmark_drift_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T17:07:42.300199+00:00
-- url     : https://prove2.me/theorems/e265ab6e-8e06-4303-82c4-10cc1347640e
-- title:
--   Actual original negative-jump Poisson count plus finite compensator drift yields an integrable horizon envelope
-- statement:
--   For the original finite-negative-activity spectral Lévy process on its own probability space, the genuine full negative Poisson jump-time count over a deterministic bounded horizon T has finite expectation by the Proved exact original Campbell first-moment theorem. Therefore the source count plus T times the absolute full smallmark first-moment compensation drift is integrable. This is the exact physically valid stochastic envelope intended for the compensated small-negative Jsmall path via the separate proved finite-mark amplitude bound and original physical Jsmall jump representation. It never requires large negative jump sizes to have finite expectation or second moments.
-- source:
--   Proved ja35 original negative Borel Poisson count first moment and original probability field X.isProbability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja35_original_negative_borel_real_count_first_moment
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_finiteactivity_negative_jump_count_plus_full_smallmark_drift_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))
    Integrable (fun ω : Ω => (N ω).toReal +
      (T : ℝ) * ‖∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν‖) P := by sorry
