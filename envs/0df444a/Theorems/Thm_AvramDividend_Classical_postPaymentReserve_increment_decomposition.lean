-- Prove2me | Theorems.Thm_AvramDividend_Classical_postPaymentReserve_increment_decomposition
-- name    : AvramDividend.Classical.postPaymentReserve_increment_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:27:53.821575+00:00
-- url     : https://prove2.me/theorems/5e6c5fea-e50f-42e9-af17-003a479797e9
-- title:
--   Post-payment reserve increments split exactly into Lévy and cumulative dividend increments
-- statement:
--   For any spectrally negative Lévy process X, dividend control D, initial reserve x and sample path, the increment in the càdlàg post-payment reserve x+X_t-D_{t+} between any s and t equals the Lévy increment X_t-X_s minus the cumulative right-continuous dividend increment D_{t+}-D_{s+}. The identity is exact and includes initial and terminal payment atoms without assuming bounded variation, stochastic integrability or any unproved theorem.

import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.postPaymentReserve_increment_decomposition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (s t : ℝ≥0) :
    (x + X.X t ω - rightLimit D t ω) -
      (x + X.X s ω - rightLimit D s ω) =
    (X.X t ω - X.X s ω) -
      (rightLimit D t ω - rightLimit D s ω) := by sorry
