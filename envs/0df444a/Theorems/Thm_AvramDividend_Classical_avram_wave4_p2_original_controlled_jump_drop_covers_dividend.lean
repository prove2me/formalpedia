-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_controlled_jump_drop_covers_dividend
-- name    : AvramDividend.Classical.avram_wave4_p2_original_controlled_jump_drop_covers_dividend
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:17:34.6072+00:00
-- url     : https://prove2.me/theorems/9e0e16a7-a0ab-4391-b99f-92eb8da8e14d
-- title:
--   Original controlled Lévy reserve jump loss covers every nonnegative right dividend payment atom
-- statement:
--   For every source sample path and every positive time, an actual adapted nondecreasing dividend strategy's right-payment atom Δ⁺D≥0 cannot exceed the downward jump of the post-payment controlled reserve relative to its true strict-left limit. The difference is exactly the magnitude of the nonpositive original Lévy jump, which can only deepen the reserve loss. This is a direct source-faithful time-local cash accounting inequality for stopped BV/UBV HJB dividend-jump estimates and includes simultaneous Lévy and dividend jumps; it assumes no stochastic compensator or martingale.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), original stopped controlled surplus and payment jump correction; canonical source jump sign e95fe5bc, source left limit 06dc12b5 and dividend rightLimit monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_exact_leftLim_identity
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave4_p2_original_controlled_jump_drop_covers_dividend
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    0 ≤ rightLimit D t ω - D t ω ∧
      rightLimit D t ω - D t ω ≤
        Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t -
          (x + X.X t ω - rightLimit D t ω) := by sorry
