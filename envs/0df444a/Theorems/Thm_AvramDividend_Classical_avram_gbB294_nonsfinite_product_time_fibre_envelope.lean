-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB294_nonsfinite_product_time_fibre_envelope
-- name    : AvramDividend.Classical.avram_gbB294_nonsfinite_product_time_fibre_envelope
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T08:03:34.697717+00:00
-- url     : https://prove2.me/theorems/455c9b57-a9c7-493c-8247-86179d8afd29
-- title:
--   Original product-time fibre envelope on the non-s-finite measure branch
-- statement:
--   Resolve the original fibre envelope when P is not s-finite, outside the hypotheses of symmetric Tonelli. Either prove the required one-sided inequality directly or establish a source-backed counterexample. This is the exact unresolved case remaining after splitting by SFinite P.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB294_nonsfinite_product_time_fibre_envelope
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (hNotSF : ¬ SFinite P)
    (S : Set (Ω × ℝ)) (hS : MeasurableSet S)
    (g : ℝ → ℝ≥0∞)
    (hFibre : ∀ t : ℝ, P ((fun ω : Ω => (ω, t)) ⁻¹' S) ≤ g t) :
    (P.prod volume) S ≤ ∫⁻ t : ℝ, g t ∂volume := by sorry
