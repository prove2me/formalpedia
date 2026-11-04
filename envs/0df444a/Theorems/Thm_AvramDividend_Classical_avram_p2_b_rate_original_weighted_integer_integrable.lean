-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_weighted_integer_integrable
-- name    : AvramDividend.Classical.avram_p2_b_rate_original_weighted_integer_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:21:41.574772+00:00
-- url     : https://prove2.me/theorems/4f164734-dd89-4d41-979a-c08305c7edf1
-- title:
--   Original spectrally negative Lévy weighted integer exponential integrability
-- statement:
--   On the genuine original spectrally negative Lévy process, for any nonnegative exponential slope and integer image moment, the fourth-power weighted exponential image is integrable. Expand the weight into five ordinary exponential moments and invoke the original X.laplace field; no jump-rate assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_original_weighted_integer_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (k : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable
      (fun ω => (Real.exp (θ * X.X t ω)) ^ k *
        (Real.exp (θ * X.X t ω) - 1) ^ 4) P := by sorry
