-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn9_original_centered_stopped_source_prefix_mean_zero
-- name    : AvramDividend.Classical.avram_bv_env3_turn9_original_centered_stopped_source_prefix_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:09:11.518477+00:00
-- url     : https://prove2.me/theorems/319fa0f2-4492-4bdc-b17c-c6363a62e0be
-- title:
--   Centred original stopped source-grid prefix has mean zero
-- statement:
--   For the original finite physical-grid source increments, assume each cell is integrable and each event-selected increment has zero expectation, as delivered by an actual predictable compensated Lévy jump theorem. Then a measurable bounded random number of those cells has an integrable zero-mean finite sum. The variable upper limit is rewritten as a fixed range with measurable indicators.
-- source:
--   A conditional analytic composition step for original predictable finite-band compensated mean-zero helpers (e.g. P3-E2 7f86a550, P3-GRID3 prefix cardinal 53697545, BV-ENV3 measurable selector fbb734fc). Does not assume that unselected zero-mean increments remain centred without predictability; event-selected hMean is explicitly required. Supports c1e2f021 signed Fatou witnesses.

import Mathlib

open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn9_original_centered_stopped_source_prefix_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (m : ℕ) (k : Ω → ℕ)
    (hk : Measurable k) (hkBound : ∀ ω, k ω ≤ m)
    (f : ℕ → Ω → ℝ) (hf : ∀ i, Integrable (f i) P)
    (hMean : ∀ i < m,
      (∫ ω, (if i < k ω then f i ω else 0) ∂P) = 0) :
    (∫ ω, ∑ i ∈ Finset.range (k ω), f i ω ∂P) = 0 := by sorry
