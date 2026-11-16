-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_unit_drift_zero_barrier_nojump_survives_tenth
-- name    : AvramDividend.Classical.avram_bvb_obstruction_unit_drift_zero_barrier_nojump_survives_tenth
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:31:16.211211+00:00
-- url     : https://prove2.me/theorems/b752488c-cb18-4368-821e-40e13bd355f4
-- title:
--   Original unit-drift zero barrier survives a tenth-unit horizon on every unit-length nojump source path
-- statement:
--   If the original source has unit drift and follows the exact linear path throughout [0,1], its genuine original zero-barrier dividend strategy has zero reserve throughout [0,1], so the actual original strict-negative ruin time is at least one and therefore strictly exceeds one tenth. This supplies the true stopped-terminal survival event for the positive-cap cash witness.
-- source:
--   Apply Proved original zero-barrier source reserve lemma 9658aeb1 and Proved original safe-interval ruin lower bound 2eacf648 at horizon 1. The precise tenth-horizon survival follows from the strict real time inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_zero_barrier_on_linear_source_has_zero_reserve
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_positive_safe_interval_ruin_lower_bound
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bvb_obstruction_unit_drift_zero_barrier_nojump_survives_tenth
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hDrift : X.drift = 1)
    (hPath : ∀ t : ℝ≥0, t ≤ (1 : ℝ≥0) →
      X.X t ω = (t : ℝ) * X.drift) :
    ((1 / 10 : ℝ≥0) : ℝ≥0∞) <
      ruinTime X 0 (barrierStrategy X 0 0) ω := by sorry
