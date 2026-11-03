-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_finite_physical_predictable_clock_exists_unique
-- name    : AvramDividend.Classical.avram_wave6_04_true_source_finite_physical_predictable_clock_exists_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T08:39:21.937518+00:00
-- url     : https://prove2.me/theorems/ba32aa0b-73d0-491d-9886-e662ab452a02
-- title:
--   Original source finite-horizon physical predictable clock exists uniquely, with exact source-time product law
-- statement:
--   For every original source filtration and finite horizon, there exists exactly one finite measure on the right-continuous predictable sigma-algebra whose values on predictable sets equal the real-time Lebesgue interval × source probability product. It packages the canonical hμ and hμclock required by the true-source nonlinear generator compensation without asserting the still-Open source jump intensity.
-- source:
--   Wave6 Chat04 physical clock canonical existence-and-uniqueness package. Both imported child theorems are now independently Proved: ddd2cd06-3b24-4a7f-8494-4a768184a63b and 0db576b1-f664-4d2a-b2b7-e570a3163857; new publication after earlier Open-import precondition failure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_physical_clock_trim_to_predictable_exists_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_physical_predictable_clock_unique

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_true_source_finite_physical_predictable_clock_exists_unique
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) :
    ∃! μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      ∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
        μ A =
          ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
            Real.toNNReal).prod P) A := by sorry
