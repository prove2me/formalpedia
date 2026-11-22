-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_original_masked_three_martingales_positiveclock_expected_budget
-- name    : AvramDividend.Classical.avram_original_masked_three_martingales_positiveclock_expected_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T22:18:30.841796+00:00
-- url     : https://prove2.me/theorems/203e3cde-dd7f-447f-a7c3-0fc180e8e341
-- title:
--   Three centred original-source signed residuals bound the strictly-positive stopping-clock event
-- statement:
--   An integrable original stopped reward F on a measurable nonnegative random clock has an event-restricted expected budget as soon as the true zero-clock-masked reward is dominated a.e. by initial b plus three integrable zero-mean original source noises and two nonpositive signed drift/payment losses. The proof keeps the zero-clock event inside the physical probability law; it is exactly the step needed to reuse the existing Avram original Ito witness.
-- source:
--   Extracted reusable mathematical bridge for Avram positive-clock rightmesh source bc89df64. Uses actual zero-clock-masked martingale domination and original real integrals; no replacement process or assumption of the sought positive-event budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_original_masked_three_martingales_positiveclock_expected_budget
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (ρ : Ω → ℝ≥0) (hρmeas : Measurable ρ)
    (F : Ω → ℝ) (hFI : Integrable F P) (b : ℝ)
    (Mc Ms Ml G R : Ω → ℝ)
    (hMcI : Integrable Mc P) (hMsI : Integrable Ms P)
    (hMlI : Integrable Ml P)
    (hMc0 : (∫ ω, Mc ω ∂P) = 0)
    (hMs0 : (∫ ω, Ms ω ∂P) = 0)
    (hMl0 : (∫ ω, Ml ω ∂P) = 0)
    (hG : ∀ᵐ ω ∂P, G ω ≤ 0)
    (hR : ∀ᵐ ω ∂P, R ω ≤ 0)
    (hSigned : ∀ᵐ ω ∂P,
      (if ρ ω = 0 then b else F ω) ≤
        b + Mc ω + Ms ω + Ml ω + G ω + R ω) :
    (∫ ω in {ω : Ω | ρ ω ≠ 0}, F ω ∂P) ≤
      b * (P {ω : Ω | ρ ω ≠ 0}).toReal := by sorry
