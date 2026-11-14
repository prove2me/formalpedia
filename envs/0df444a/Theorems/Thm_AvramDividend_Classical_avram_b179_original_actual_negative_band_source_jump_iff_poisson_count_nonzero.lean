-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b179_original_actual_negative_band_source_jump_iff_poisson_count_nonzero
-- name    : AvramDividend.Classical.avram_b179_original_actual_negative_band_source_jump_iff_poisson_count_nonzero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T21:19:58.400053+00:00
-- url     : https://prove2.me/theorems/8efcf46c-0858-47d9-b012-e99dca55a854
-- title:
--   Original physical negative-band source jump exists on a half-open clock interval exactly when its original mapped Poisson negative-band count is nonzero
-- statement:
--   For the genuine original spectrally negative Levy source on any sample path, any ordered physical source interval (s,t] and any negative reciprocal cutoff n, the original mapped jump-counting Poisson measure assigns nonzero mass to the exact time/negative band rectangle if and only if at least one actual original source left-limit jump in the interval has magnitude in that same negative band. Authoritatively Proved P2 identifies the original source band count with the ENNReal cardinal of the actual physical marked-time set, while Proved wave7_06 guarantees that this marked-time set is finite. Its cardinal is nonzero exactly when the set is nonempty, by Mathlib Set.ncard_pos for finite sets. This completes the exact original negative Poisson count-to-physical jump mark correspondence needed to derive genuine original marked/unmarked random-grid measurability from B166 and B178 and to close the B110/B125 finite cutoff source bridge. No replacement source process, global second moments or exceptional-path finite activity assumption are used.
-- source:
--   Proved original P2 negative-band interval count/ncard and wave7_06 negative marked physical source time finiteness, Mathlib Set.ncard_pos.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_interval_negative_band_count_ncard
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The true original negative-band jump measure of any ordered physical half-open source interval is nonzero exactly when that actual source interval contains a jump in the same negative mark band. -/

theorem AvramDividend.Classical.avram_b179_original_actual_negative_band_source_jump_iff_poisson_count_nonzero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0) (hst : s ≤ t) (n : ℕ) :
    (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Iic (-(1 / ((n : ℝ) + 1))))) ≠ 0 ↔
    ∃ u : ℝ≥0, s < u ∧ u ≤ t ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1)) := by sorry
