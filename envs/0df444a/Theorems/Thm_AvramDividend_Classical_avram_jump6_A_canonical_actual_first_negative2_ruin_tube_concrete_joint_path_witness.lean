-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_canonical_actual_first_negative2_ruin_tube_concrete_joint_path_witness
-- name    : AvramDividend.Classical.avram_jump6_A_canonical_actual_first_negative2_ruin_tube_concrete_joint_path_witness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T16:13:18.119172+00:00
-- url     : https://prove2.me/theorems/1ece700e-94a7-4a0c-8200-8b55300ae41c
-- title:
--   Construct a concrete authentic canonical Brownian plus first negative-two Poisson sample path with small tube and exact first-jump count
-- statement:
--   The actual native canonical standard Brownian law gaussianLimit and the genuine rate-one negative-size-two compound Poisson driver possess at least one joint sample path on which the centred Brownian fluctuation remains below 1/4000 through 17/16000 (including the drifted tube), the true first Poisson interarrival lies strictly between zero and 17/16000, the actual marked count is zero at every strictly earlier time, and exactly one at the first mark. This is a source-faithful concrete witness, extracted from the already-Proved strictly positive genuine product event 48dc7b4e. It can be used to instantiate original spectrally negative Lévy first-ruin countermodels for the deprecated fixed unit-mark spatial cash certificate.

import Mathlib
import Definitions.Def_GlynnSTS_Limit_Setting
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_canonical_native_Brownian_gaussian_and_actual_firstmark_full_count_joint_positive
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_canonical_actual_first_negative2_ruin_tube_concrete_joint_path_witness
    [IsProbabilityMeasure gaussianLimit]
    {ΩJ : Type*} [MeasurableSpace ΩJ]
    (μJ : Measure ΩJ) (τ Y : ℕ → ΩJ → ℝ)
    (hJ : IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      (Measure.dirac (-2 : ℝ)) μJ) :
    ∃ (ωB : ℝ≥0 → ℝ) (ωJ : ΩJ),
      (∀ s : unitInterval,
        s ≤ (⟨(17 / 16000 : ℝ),
          by constructor <;> norm_num⟩ : unitInterval) →
          |ProbabilityTheory.brownian ⟨s, s.2.1⟩ ωB -
            ProbabilityTheory.brownian 0 ωB| < (1 / 4000 : ℝ) ∧
          |ProbabilityTheory.brownian ⟨s, s.2.1⟩ ωB -
            ProbabilityTheory.brownian 0 ωB +
            2 * (s : ℝ)| < (1 / 400 : ℝ)) ∧
      0 < τ 0 ωJ ∧
      (∀ t : ℝ≥0, (t : ℝ) < arrival τ 0 ωJ →
        jumpCount (fun n => arrival τ n ωJ) (t : ℝ) = 0) ∧
      jumpCount (fun n => arrival τ n ωJ) (arrival τ 0 ωJ) = 1 ∧
      τ 0 ωJ ≤ (17 / 16000 : ℝ) := by sorry
