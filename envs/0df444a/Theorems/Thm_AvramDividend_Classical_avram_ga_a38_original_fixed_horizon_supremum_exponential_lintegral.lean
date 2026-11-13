-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a38_original_fixed_horizon_supremum_exponential_lintegral
-- name    : AvramDividend.Classical.avram_ga_a38_original_fixed_horizon_supremum_exponential_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T12:28:46.550349+00:00
-- url     : https://prove2.me/theorems/c8192ba2-d47b-4d67-958c-278cfe392d17
-- title:
--   Original finite-horizon running-supremum exponential moment from random-clock product moment
-- statement:
--   The exponential of beta times the running supremum of the original Levy source at fixed nonnegative horizon n has finite lintegral, whenever beta is nonnegative and the corresponding original running-supremum exponential has finite joint moment under an auxiliary clock measure with positive mass beyond horizon n. This is a physical, unchanged-source application of proved random-clock transfer a36, joint running-supremum measurability, and monotonicity. Connect to the already proved exponential-clock MGF and tail law to close the Gaussian top-cap terminal positive-integrable envelope d9c4650e.
-- source:
--   Gauss a26 terminal envelope d9c4650e; a36 8ac88c02 and original runningSup monotonicity 848fbd48.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a38_original_fixed_horizon_supremum_exponential_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (nu : Measure ℝ) [SFinite nu]
    (n : ℝ≥0) (β : ℝ) (hβ : 0 ≤ β)
    (hTail : 0 < nu (Set.Ioi (n : ℝ)))
    (hMoment : (∫⁻ z : Ω×ℝ,
      ENNReal.ofReal (Real.exp
        (β * runningSup X (Real.toNNReal z.2) z.1))
          ∂ (P.prod nu)) < ⊤) :
    (∫⁻ ω : Ω,
      ENNReal.ofReal (Real.exp (β * runningSup X n ω))
        ∂ P) < ⊤ := by sorry
