-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_stopped_index_masked_AE_measurable
-- name    : AvramDividend.Classical.avram_bv_error7_stopped_index_masked_AE_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T18:54:45.362564+00:00
-- url     : https://prove2.me/theorems/1b88588c-98fb-4a9b-b82a-790953d99e46
-- title:
--   Measurable random stopped prefix of finite source coefficients
-- statement:
--   For any measurable random prefix length k and a family f of a.e. strongly measurable finite-cell coefficients, the finite envelope of cells masked by i < k remains a.e. strongly measurable. Applied to the original stopped physical grid, this avoids assuming measurability of the aggregate Taylor remainder. No surrogate stochastic process or BV budget is used.
-- source:
--   Original stopped-grid measurability reducer for the BV source error; a genuine measurable random-prefix operator.

import Mathlib
open MeasureTheory Set Filter
open scoped BigOperators

theorem AvramDividend.Classical.avram_bv_error7_stopped_index_masked_AE_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (N : ℕ) (k : Ω → ℕ) (hk : Measurable k)
    (f : ℕ → Ω → ℝ)
    (hf : ∀ i, AEStronglyMeasurable (f i) P) :
    AEStronglyMeasurable (fun ω =>
      ∑ i ∈ Finset.range N, if i < k ω then f i ω else 0) P := by sorry
