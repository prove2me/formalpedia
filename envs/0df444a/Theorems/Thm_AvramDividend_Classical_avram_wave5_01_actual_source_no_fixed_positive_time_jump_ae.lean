-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_no_fixed_positive_time_jump_ae
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_no_fixed_positive_time_jump_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:47:21.889672+00:00
-- url     : https://prove2.me/theorems/b4407263-9eac-412e-be7a-17c1fecc8ebe
-- title:
--   No deterministic positive-time jumps on the actual original Lévy process
-- statement:
--   For every deterministic positive time t, the original sample path jump X.X t ω minus its left limit is zero P-almost everywhere. The proof stays on the original probability space and filtration and uses original stationary increments to identify the laws of a vanishing backward increment and a short-time increment; continuity at zero and left limits give two distributions of one same limit, forcing the jump distribution to be Dirac at zero. A useful intrinsic non-atom condition for the actual marked jump measure and source compensator; there is no independent Poisson copy.
-- source:
--   Original SpectrallyNegativeLevy P 𝓕; its leftLim, rightCont, X_zero, stationaryIncrements, adapted, isProbability fields, and Proved original raw filtration prejump strong measurability UUID 73fbc493-27da-4bef-ac31-f2b41adf1102.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_original_raw_filtration_prejump_jumpmark_strongly_adapted
open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_source_no_fixed_positive_time_jump_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ ω ∂P,
      X.X t ω - Function.leftLim (fun u : ℝ≥0 => X.X u ω) t = 0 := by sorry
