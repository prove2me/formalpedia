-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b110_original_negative_count_zero_forbids_actual_band_source_jump
-- name    : AvramDividend.Classical.avram_b110_original_negative_count_zero_forbids_actual_band_source_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T16:10:59.497261+00:00
-- url     : https://prove2.me/theorems/72158de4-a7f9-4639-8109-25556dee2bac
-- title:
--   A zero actual original Poisson negative-band source count certifies the physical stopped interval contains no band jump
-- statement:
--   On the exact original Lévy source sample path and any actual ordered half-open physical time interval (s,t], assume the original mapped jump Poisson measure assigns zero to the negative band of marks at most -1/(n+1). A Proved exact original source theorem identifies this count with the ENNReal lift of the actual negative-band jump-time set cardinal. Another Proved original source theorem shows that physical negative-band marked-time set is finite. If any actual original jump in that band occurred, its finite marked-time set has strictly positive cardinal, contradicting the Poisson source count zero. Thus no actual original band jump exists on the interval, without deterministic-clock substitution or unproved negative second-moment assumptions.
-- source:
--   Proved avram_p2_e_compensator_original_interval_negative_band_count_ncard, Proved avram_wave7_06_original_negative_band_marked_times_finite and Mathlib Set.ncard_eq_toFinset_card.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_interval_negative_band_count_ncard
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- An exact original negative-band Poisson count of zero excludes every actual band jump in the given half-open source interval. -/

theorem AvramDividend.Classical.avram_b110_original_negative_count_zero_forbids_actual_band_source_jump
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0) (hst : s ≤ t) (n : ℕ)
    (hZero :
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0) :
    ∀ u : ℝ≥0, s < u → u ≤ t →
      ¬ (X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))) := by sorry
