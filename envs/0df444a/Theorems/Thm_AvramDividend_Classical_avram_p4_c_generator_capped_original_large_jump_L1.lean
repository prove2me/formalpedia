-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_capped_original_large_jump_L1
-- name    : AvramDividend.Classical.avram_p4_c_generator_capped_original_large_jump_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:11:31.569623+00:00
-- url     : https://prove2.me/theorems/447457d7-e29d-41cd-8c51-41f309da8779
-- title:
--   Original finite-intensity large negative raw jump kernel is integrable uniformly across capped reserves including zero
-- statement:
--   For the original Lévy X and a payoff continuous on nonnegative reserves and zero on negative reserves, every capped reserve state y in [0,v], including y=0, has a ν-integrable large negative raw-jump increment on z<-epsilon. This uses the three independently source-backed P4-C proofs of payoff measurability, cap-wide mark bound, and bounded integrand with separated Lévy finite tail. It avoids an unjustified generator or C² hypothesis at ruin and supports finite-intensity stopped compensation.
-- source:
--   P4-C zero_negative_payoff_measurable, large_raw_uniform_on_prejump_cap, large_raw_integrable_of_bound (must be Proved before proof submission)

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_capped_original_large_jump_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ)
    (v ε : ℝ) (hv : 0 ≤ v) (hε : 0 < ε)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ t : ℝ, t < 0 → w t = 0) :
    ∀ y ∈ Icc 0 v,
      IntegrableOn (fun z : ℝ => w (y + z) - w y)
        (Iio (-ε)) X.ν := by sorry
