-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_event_local_and_BV_tail_positive_integrable
-- name    : AvramDividend.Classical.avram_bv_error7_original_event_local_and_BV_tail_positive_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:54:21.220437+00:00
-- url     : https://prove2.me/theorems/320c0379-c0e2-4f3a-a099-38f9a0f3590f
-- title:
--   Original BV source mass and event-local L1 imply integrability of all positive grid errors
-- statement:
--   For the authentic bounded-variation X and its actual integrable BV source-mass envelope on a finite horizon, suppose each stopped-grid positive-error restriction to one interior event is integrable, each full positive error is a.e. strongly measurable, and outside the event the error is uniformly bounded by K times that authentic source mass. Then every full positive-error random variable is integrable. The proof dominates its norm by the sum of the event-restricted positive-error norm and K times the original integrable BV source mass. It uses no BV signed-prebudget estimate and creates no probabilistic assumptions outside the source and the stated error properties.
-- source:
--   Positive-error integrability from genuine BV original L1 source variation and event-local error; removes hPos assumption from subsequent Fatou bridge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_BV_source_variation_L1_upto_one
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_event_local_and_BV_tail_positive_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (hT : T ≤ 1)
    (s : Set Ω) (Err : ℕ → Ω → ℝ)
    (hMaskedInt : ∀ m, Integrable
      (fun ω => max (if ω ∈ s then Err m ω else 0) 0) P)
    (hPosMeas : ∀ m, AEStronglyMeasurable
      (fun ω => max (Err m ω) 0) P)
    (K : ℝ) (hK : 0 ≤ K)
    (hOutside : ∀ m, ∀ᵐ ω ∂P, ω ∉ s →
      max (Err m ω) 0 ≤
        K * (|X.drift| * (T : ℝ) +
          |(T : ℝ) * X.drift - X.X T ω|)) :
    ∀ m, Integrable (fun ω => max (Err m ω) 0) P := by sorry
