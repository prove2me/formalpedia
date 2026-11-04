-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_fourth_weight_integrable
-- name    : AvramDividend.Classical.avram_p2_b_rate_original_fourth_weight_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:32:25.30931+00:00
-- url     : https://prove2.me/theorems/615ef4e8-635b-4152-8738-83a0039cabb8
-- title:
--   Original Lévy fourth exponential mark weight is integrable
-- statement:
--   For the actual spectrally negative Lévy process on its own probability measure and any nonnegative theta and time t, the nonnegative fourth-exponential weight (exp(theta X_t)-1)^4 is Bochner integrable. The proof uses only the original X.laplace integrability axiom for each rate k*theta, k=0,...,4, and the binomial polynomial expansion. This removes a key integrability blocker from converting the original fourth-weight derivative into a negative-increment O(h) bound; no jump-rate identity is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_original_fourth_weight_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable
      (fun ω => (Real.exp (θ * X.X t ω) - 1) ^ 4) P := by sorry
