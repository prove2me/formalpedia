-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_native_gaussian_physical_size2_first_mark_joint_short_tube_positive
-- name    : AvramDividend.Classical.avram_jump6_A_native_gaussian_physical_size2_first_mark_joint_short_tube_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T09:43:41.819143+00:00
-- url     : https://prove2.me/theorems/44c05a9d-9f0d-4ee8-9680-66f041e6219f
-- title:
--   Canonical native Brownian and physical size-two Poisson first-mark short event has positive true joint probability
-- statement:
--   On the canonical gaussianLimit sample-path space and an actual independent compound-Poisson physical driver of rate one and mark -2, the product probability of the native centred Brownian tube |W_s−W_0|<1/4000 for every s up to 1/1000 and the genuine first negative jump by the same 1/1000 clock is strictly positive. Uses Proved canonical native Gaussian tube f1b21611, actual first-mark CDF 25d358c8, and the exact Measure.prod_prod rectangle mass. This is stronger than the previous abstract IsStdBMC product source: the canonical paths can be matched directly with the existing Brownian-Poisson Lévy model assembly.

import Mathlib
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_GlynnSTS_Limit_Setting
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_ProbabilityTheory_isBrownianReal_brownian_avram
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_native_gaussian_physical_size2_first_mark_joint_short_tube_positive
    [IsProbabilityMeasure gaussianLimit]
    {ΩJ : Type*} [MeasurableSpace ΩJ]
    (μJ : Measure ΩJ) (τ Y : ℕ → ΩJ → ℝ)
    (hJ : IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      (Measure.dirac (-2 : ℝ)) μJ) :
    0 < (gaussianLimit.prod μJ)
      ({ωB : ℝ≥0 → ℝ | ∀ s : unitInterval,
          s ≤ (⟨(1 / 1000 : ℝ), by constructor <;> norm_num⟩ : unitInterval) →
            |ProbabilityTheory.brownian ⟨s, s.2.1⟩ ωB -
                ProbabilityTheory.brownian 0 ωB| < (1 / 4000 : ℝ)} ×ˢ
        {ωJ : ΩJ | τ 0 ωJ ≤ (1 / 1000 : ℝ)}) := by sorry
