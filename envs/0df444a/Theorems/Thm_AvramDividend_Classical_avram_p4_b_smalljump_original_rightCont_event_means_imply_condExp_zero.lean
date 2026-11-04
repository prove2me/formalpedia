-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_rightCont_event_means_imply_condExp_zero
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_rightCont_event_means_imply_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:42:29.769195+00:00
-- url     : https://prove2.me/theorems/a3b46bfb-bbdd-4cd0-a800-d4b1410433c1
-- title:
--   Original predictable all-event zero means imply right-continuous conditional centring
-- statement:
--   If a finite-band original spectrally negative Lévy jump increment V is integrable and its integral over every event measurable at time s in the source right-continuous filtration is zero, then its conditional expectation given that sigma algebra vanishes. This converts P2's future/past weighted compensation to the martingale-difference hypothesis used for the small-jump L² isometry. The all-event compensation identity is explicit and remains unproved until P2 supplies it, including the right-continuous filtration extension.
-- source:
--   Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic ae_eq_condExp_of_forall_setIntegral_eq, original source 𝓕.rightCont.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory AvramDividend.Classical
open scoped ENNReal NNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_rightCont_event_means_imply_condExp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (V : Ω → ℝ)
    (hVint : Integrable V P)
    (hEventZero : ∀ A : Set Ω,
      MeasurableSet[𝓕.rightCont s] A →
      (∫ ω in A, V ω ∂P) = 0) :
    P[V | 𝓕.rightCont s] =ᵐ[P] 0 := by sorry
