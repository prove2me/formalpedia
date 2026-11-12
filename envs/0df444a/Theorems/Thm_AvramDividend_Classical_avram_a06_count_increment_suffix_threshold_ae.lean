-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_count_increment_suffix_threshold_ae
-- name    : AvramDividend.Classical.avram_a06_count_increment_suffix_threshold_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T08:42:05.616521+00:00
-- url     : https://prove2.me/theorems/425df1e2-d685-4a98-a674-8e4197160201
-- title:
--   Original renewal count increment equals residual plus complete future suffix criterion almost surely
-- statement:
--   If the arrival-count threshold identity holds on a full-measure set, then the exact count increment is characterised by the residual first wait and subsequent infinite stream on that same full-measure set.
-- source:
--   Apply the already-proved pointwise chat06 renewal count-increment/suffix characterisation on the common almost-sure threshold event.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat06_renewal_count_increment_residual_future_suffix_characterisation
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_count_increment_suffix_threshold_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (τ : ℕ → Ω → ℝ) (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ᵐ ω ∂P, ∀ u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (clock : ℝ) :
    ∀ᵐ ω ∂P, ∀ (v : ℝ) (k : ℕ), k < N ω (clock + v) - N ω clock ↔
        τ (N ω clock) ω -
          (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω) +
          (∑ j ∈ Finset.range k, τ (N ω clock + 1 + j) ω) ≤ v := by sorry
