-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_nonintegrable_signed_source_tight_error_transfer
-- name    : AvramDividend.Classical.avram_a19_nonintegrable_signed_source_tight_error_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T14:36:20.182891+00:00
-- url     : https://prove2.me/theorems/554ad83c-43c9-48ec-9cbb-903ca29323bd
-- title:
--   Dominated exact positive deficit converges in mean without integrability of signed source
-- statement:
--   An almost-surely dominated positive payoff excess is integrable and converges to zero in expected value whenever its nonnegative integrable envelope does, even if the baseline G (including its signed HJB drift) is not integrable. Requires only strong measurability of the exact positive excess.
-- source:
--   Genuine measure-theoretic transfer needed to connect physical BV-CELL7 and BV-ERROR7 source errors to the alternate original a19 nonintegrable tight-positive-excess reduction. Unlike the existing a19_integrable_tight_error_and_vanishing_expectation, no Integrable F or Integrable G premise is introduced.

import Mathlib
open Classical MeasureTheory Set Filter
noncomputable section

theorem AvramDividend.Classical.avram_a19_nonintegrable_signed_source_tight_error_transfer
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (F G Err : ℕ → Ω → ℝ)
    (hMeas : ∀ n, AEStronglyMeasurable
      (fun ω => max (F n ω - G n ω) 0) P)
    (hErr : ∀ n, Integrable (fun ω => max (Err n ω) 0) P)
    (hlim : Tendsto
      (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (nhds (0 : ℝ)))
    (hbudget : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ G n ω + max (Err n ω) 0) :
    (∀ n, Integrable (fun ω => max (F n ω - G n ω) 0) P) ∧
    Tendsto (fun n => ∫ ω, max (F n ω - G n ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by sorry
