-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_brownian_tube_and_early_size2_mark_positive_product
-- name    : AvramDividend.Classical.avram_jump6_A_actual_brownian_tube_and_early_size2_mark_positive_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:25:40.193483+00:00
-- url     : https://prove2.me/theorems/1732b362-70a0-408a-9556-6ba06a3385e3
-- title:
--   Positive original Brownian tube and early physical negative Poisson mark product event
-- statement:
--   For independent original standard Brownian continuous paths and actual size-two rate-one compound Poisson interarrival process under product probability, the joint event that Brownian path remains within 1/4000 until time 1/500 and an actual negative mark arrives by 1/10 has strictly positive probability. Combines the existing Proved Brownian tube source and the newly Proved short-time first Poisson arrival theorem using the exact product measure rectangle formula. This is part of a genuine first-jump countermodel, though it has mismatched time scales until aligned for the final stopped event.

import Mathlib
import Definitions.Def_GlynnSTS_NoAttain_Setting
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_actual_brownian_tube_and_early_size2_mark_positive_product
    {ΩB ΩJ : Type*} [MeasurableSpace ΩB] [MeasurableSpace ΩJ]
    (μB : Measure ΩB) [IsProbabilityMeasure μB]
    (μJ : Measure ΩJ)
    (B : ΩB → C(unitInterval, ℝ))
    (hB : GlynnSTS.Limit.IsStdBMC μB B)
    (τ Y : ℕ → ΩJ → ℝ)
    (hJ : IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      (Measure.dirac (-2 : ℝ)) μJ) :
    0 < (μB.prod μJ)
      ({ω : ΩB | ∀ s : unitInterval,
          s ≤ (⟨(1 / 500 : ℝ), by constructor <;> norm_num⟩ : unitInterval) →
            |B ω s| < (1 / 4000 : ℝ)} ×ˢ
       {ω : ΩJ | τ 0 ω ≤ (1 / 10 : ℝ)}) := by sorry
