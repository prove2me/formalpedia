-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_raw_event_means_imply_condExp_zero
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_raw_event_means_imply_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:46:07.731176+00:00
-- url     : https://prove2.me/theorems/54afcf5b-f54d-4e0d-b658-0d1198d9dbb3
-- title:
--   P2 raw-original-filtration all-event zero means imply conditional centring
-- statement:
--   For the original spectrally negative Lévy process and its actual filtration, if an integrable finite-band compensated random variable integrates to zero over every source-time s measurable event, then its conditional expectation given the source sigma algebra at s is zero. This is exactly the logical implication needed immediately after P2's raw predictable rectangle mean theorem; the separate right-continuous upgrade remains open.
-- source:
--   Mathlib ae_eq_condExp_of_forall_setIntegral_eq and the exact original 𝓕 s sigma algebra in the Open P2 theorem 393b03a8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory AvramDividend.Classical
open scoped ENNReal NNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_raw_event_means_imply_condExp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (V : Ω → ℝ)
    (hVint : Integrable V P)
    (hEventZero : ∀ A : Set Ω,
      MeasurableSet[𝓕 s] A →
      (∫ ω in A, V ω ∂P) = 0) :
    P[V | 𝓕 s] =ᵐ[P] 0 := by sorry
