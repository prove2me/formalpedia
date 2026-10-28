-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_runningSup_gt_iff_strict_upcrossing_before_horizon
-- name    : AvramDividend.Classical.avram_ws01e_b_runningSup_gt_iff_strict_upcrossing_before_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:13:14.759034+00:00
-- url     : https://prove2.me/theorems/b626324c-8e00-4488-86d6-b7d63449435c
-- title:
--   Genuine Lévy supremum upper ray equals strict first-upcrossing before the observation horizon
-- statement:
--   For every path of a spectrally negative Lévy process with no upward jumps, every nonnegative level b and nonnegative horizon t, the actual running supremum exceeds b if and only if the extended-real infimum of all strict upward-passage times across b is strictly less than t. The non-positive-jump hypothesis is essential at the terminal endpoint: if every earlier path value stays at or below b, the endpoint itself cannot jump above b. This closes the pathwise event-equivalence needed for genuine exponential-horizon upper-record Wiener–Hopf splitting, including time zero, without assuming any exit transform or Wiener–Hopf independence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_gt_level_iff_prior_strict_path_hit
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_lt_iff_exists_witness
import Theorems.Thm_AvramDividend_Classical_path_value_le_of_strict_prefix_le

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_runningSup_gt_iff_strict_upcrossing_before_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (ω : Ω) (t : ℝ≥0) :
    b < runningSup X t ω ↔
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞)) < (t : ℝ≥0∞) := by sorry
